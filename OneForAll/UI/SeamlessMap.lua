local _, FLT = ...

-- Quality of Life > World Map > Seamless map ("seamlessMap", 6.2.9, off by default): the continent map with
-- every zone's map drawn on it in full detail, zoomed smoothly with the mouse wheel toward the cursor and moved
-- by dragging. A left-click glides into the zone under the cursor (on the world map: the continent), a right-click
-- out to the whole continent, and from there to the world (test5, user 14.11.: keep the clicks). A zone map the game
-- opens shows as the continent, framed on that zone. The world map zooms the same way: once the continent being zoomed into fills the view the
-- map hands over to it at the same place and size, and out of a continent back to the world (6.2.9-test4, user
-- 14.11.: the jump between them was not seamless).
--
-- What is drawn: Blizzard's continent art (the map's own), and over it each zone's map pieces (Data/MapOverlays.lua,
-- the same pieces as Remove Fog) placed by C_Map.GetMapRectOnMap: the explored ones, the others only with Remove Fog. Each zone's base map is a rectangle that also
-- paints parchment over its neighbours, so it is left out (the continent's art shows between the pieces).
--
-- The zoom (an animation that keeps the point under the cursor in place, a drag mid-zoom carrying it) is adapted
-- from OpenMap (Map/WorldMap.lua, MIT, github.com/openmap-world/openmap; THIRD_PARTY_LICENSES.txt).

local SM = {}
FLT.SeamlessMap = SM

local ZOOM_STEP = 1.25        -- each wheel notch
local ZOOM_RATE = 14          -- the wheel zoom's approach, per second (in log zoom)
local GLIDE_TIME = 0.4        -- a click's glide, seconds
local DETAIL_FROM, DETAIL_FULL = 1.15, 1.9 -- zoom (1 = the continent fits) where the zones' detail fades in
local DEEPEST = 2             -- the deepest zoom: this many screen px per zone map px
local CULL_MARGIN = 0.15      -- zones this far (view sizes) outside the view still shown
local CITIES = { [1453] = true, [1454] = true, [1455] = true, [1456] = true, [1457] = true, [1458] = true }

local map, sc                 -- WorldMapFrame, its ScrollContainer
local active = false          -- the stitched art is showing (a continent map, the option on)
local anim                    -- the running wheel zoom: { u, v, sx, sy, target, down }
local wheelMode, scalingMode  -- Blizzard's, put back when not stitched
local baseFrame, pieceFrame   -- the art: zone base maps (test switch only) under the zone pieces
local continents = {}         -- continent mapID -> { zones = { ... }, deepest = scale } (built once per continent)
local focus                   -- { mapID = continent, l, r, t, b, at = GetTime() }: the zone a redirect frames
local showBase = false        -- /ofa seamlessbase: also the zones' base maps (for testing the look)

local function on() return FLT.QoL and FLT.QoL.Get("seamlessMap") end
local function clamp(x, lo, hi) if x < lo then return lo elseif x > hi then return hi end return x end

-- the canvas (the continent's art) in its own px
local function canvasSize()
  local c = sc and sc.Child
  local w, h = c and c:GetWidth() or 0, c and c:GetHeight() or 0
  if w <= 0 or h <= 0 then return 1002, 668 end
  return w, h
end
-- the view's scale where the whole canvas fits
local function fitScale()
  local W, H = canvasSize()
  return math.min(sc:GetWidth() / W, sc:GetHeight() / H)
end

--------------------------------------------------------------------------------
-- The continents' zones
--------------------------------------------------------------------------------

local function fileSize(px) local s = 16; while s < px do s = s * 2 end; return s end

local overlayCache = {}
local function overlaysOf(artID)
  local list = overlayCache[artID]
  if list then return list end
  list = {}
  for part in ((FLT.MAP_OVERLAYS or {})[artID] or ""):gmatch("[^;]+") do
    local w, h, x, y, files = part:match("^(%d+),(%d+),(%-?%d+),(%-?%d+),([%d:]+)$")
    if w then
      local ids = {}
      for id in files:gmatch("%d+") do ids[#ids + 1] = tonumber(id) end
      list[#list + 1] = { w = tonumber(w), h = tonumber(h), x = tonumber(x), y = tonumber(y), ids = ids }
    end
  end
  overlayCache[artID] = list
  return list
end

-- a rectangle inside another's: a city in its zone (their maps are drawn by the zone's already)
local function inside(a, b)
  return a.l >= b.l and a.r <= b.r and a.t >= b.t and a.b <= b.b and (a.r - a.l) * (a.b - a.t) < (b.r - b.l) * (b.b - b.t)
end

local function continent(mapID)
  if continents[mapID] ~= nil then return continents[mapID] or nil end
  continents[mapID] = false
  local info = C_Map.GetMapInfo(mapID)
  if not (info and Enum and Enum.UIMapType and info.mapType == Enum.UIMapType.Continent) then return nil end
  local zones = {}
  for _, child in ipairs(C_Map.GetMapChildrenInfo(mapID, Enum.UIMapType.Zone, false) or {}) do
    local id = child.mapID
    local l, r, t, b = C_Map.GetMapRectOnMap(id, mapID)
    local layers = C_Map.GetMapArtLayers and C_Map.GetMapArtLayers(id)
    local layer = layers and layers[1]
    local artID = C_Map.GetMapArtID and C_Map.GetMapArtID(id)
    if not CITIES[id] and l and r > l and b > t and layer and layer.layerWidth and layer.layerWidth > 0 and artID then
      zones[#zones + 1] = { mapID = id, l = l, r = r, t = t, b = b, artID = artID, layer = layer }
    end
  end
  local keep = {}
  for _, z in ipairs(zones) do
    local city = false
    for _, o in ipairs(zones) do if o ~= z and inside(z, o) then city = true; break end end
    if not city then keep[#keep + 1] = z end
  end
  if #keep < 2 then return nil end
  local c = { mapID = mapID, zones = keep, byZone = {} }
  for _, z in ipairs(keep) do c.byZone[z.mapID] = z end
  continents[mapID] = c
  return c
end

-- a world map with stitched continents on it: { mapID, conts = { { mapID, l, r, t, b } }, byCont }
local worlds = {}
local function worldOf(mapID)
  if not mapID then return nil end
  if worlds[mapID] ~= nil then return worlds[mapID] or nil end
  worlds[mapID] = false
  local info = C_Map.GetMapInfo(mapID)
  if not (info and info.mapType == Enum.UIMapType.World) then return nil end
  local w = { mapID = mapID, conts = {}, byCont = {} }
  for _, child in ipairs(C_Map.GetMapChildrenInfo(mapID, Enum.UIMapType.Continent, false) or {}) do
    local l, r, t, b = C_Map.GetMapRectOnMap(child.mapID, mapID)
    if l and r > l and b > t and continent(child.mapID) then
      local c = { mapID = child.mapID, l = l, r = r, t = t, b = b }
      w.conts[#w.conts + 1] = c
      w.byCont[child.mapID] = c
    end
  end
  if #w.conts == 0 then return nil end
  worlds[mapID] = w
  return w
end
-- the continent on the world at (u, v): the smallest whose rectangle holds it
local function continentAt(w, u, v)
  local best, area
  for _, c in ipairs(w.conts) do
    if u >= c.l and u <= c.r and v >= c.t and v <= c.b then
      local a = (c.r - c.l) * (c.b - c.t)
      if not best or a < area then best, area = c, a end
    end
  end
  return best
end
-- the world a continent hands over to when zoomed out of, and its place there
local function worldAbove(mapID)
  local info = C_Map.GetMapInfo(mapID)
  local w = info and worldOf(info.parentMapID)
  local c = w and w.byCont[mapID]
  if c then return w, c end
end

-- the continent a zone map belongs to, when that continent is stitched
local function continentOf(mapID)
  local info = mapID and C_Map.GetMapInfo(mapID)
  if not (info and info.mapType == Enum.UIMapType.Zone) then return nil end
  local parent = info.parentMapID
  local c = parent and continent(parent)
  if not c then return nil end
  local z = c.byZone[mapID]
  if z then return c, z end
  -- a city: framed on its own rectangle
  local l, r, t, b = C_Map.GetMapRectOnMap(mapID, parent)
  if l and r > l and b > t then return c, { l = l, r = r, t = t, b = b } end
  return nil
end

-- the textures of one zone, made the first time it shows (canvas px: the canvas scales them)
local function buildZone(z)
  if z.tex then return end
  z.tex = {}
  local W, H = canvasSize()
  local L = z.layer
  local lw, lh = L.layerWidth, L.layerHeight
  local fx, fy = (z.r - z.l) * W / lw, (z.b - z.t) * H / lh -- canvas px per zone map px
  local ox, oy = z.l * W, z.t * H
  local TW, TH = L.tileWidth or 256, L.tileHeight or 256
  z.pieces = {}
  local function tile(frame, layer, id, x, y, pw, ph, fw, fh)
    local t = frame:CreateTexture(nil, layer)
    t:SetTexture(id, nil, nil, "TRILINEAR")
    t:SetTexCoord(0, pw / fw, 0, ph / fh)
    t:SetSize(pw * fx, ph * fy)
    t:SetPoint("TOPLEFT", frame, "TOPLEFT", ox + x * fx, -(oy + y * fy))
    z.tex[#z.tex + 1] = t
    return t
  end
  if showBase then
    local files = C_Map.GetMapArtLayerTextures and C_Map.GetMapArtLayerTextures(z.mapID, 1)
    if files then
      local wide, tall = math.ceil(lw / TW), math.ceil(lh / TH)
      for j = 1, tall do
        for k = 1, wide do
          local id = files[(j - 1) * wide + k]
          local pw, ph = math.min(TW, lw - TW * (k - 1)), math.min(TH, lh - TH * (j - 1))
          if id and pw > 0 and ph > 0 then tile(baseFrame, "ARTWORK", id, TW * (k - 1), TH * (j - 1), pw, ph, TW, TH) end
        end
      end
    end
  end
  -- the pieces, tiled as the game tiles its explored ones (UI/MapFog.lua); each keyed by its offset like the
  -- game's explored ones, so it shows or hides with the exploration (applyFog)
  for _, o in ipairs(overlaysOf(z.artID)) do
    local piece = { key = o.x .. "," .. o.y, tex = {} }
    z.pieces[#z.pieces + 1] = piece
    local wide, tall = math.ceil(o.w / TW), math.ceil(o.h / TH)
    for j = 1, tall do
      local ph, fh = TH, TH
      if j == tall then ph = o.h % TH; if ph == 0 then ph = TH end; fh = fileSize(ph) end
      for k = 1, wide do
        local pw, fw = TW, TW
        if k == wide then pw = o.w % TW; if pw == 0 then pw = TW end; fw = fileSize(pw) end
        local id = o.ids[(j - 1) * wide + k]
        if id then piece.tex[#piece.tex + 1] = tile(pieceFrame, "ARTWORK", id, o.x + TW * (k - 1), o.y + TH * (j - 1), pw, ph, fw, fh) end
      end
    end
  end
end

-- Unexplored parts as on the zone maps: only with Remove Fog ("mapFog"), as visible as its slider says
-- ("mapFogAlpha"); explored ones always. The explored list is asked once per zone until it changes.
local function applyFog(z)
  if not z.explored then
    z.explored = {}
    local got = C_MapExplorationInfo and C_MapExplorationInfo.GetExploredMapTextures
      and C_MapExplorationInfo.GetExploredMapTextures(z.mapID)
    for _, e in ipairs(got or {}) do z.explored[e.offsetX .. "," .. e.offsetY] = true end
  end
  local fog = FLT.QoL.Get("mapFog") and (tonumber(FLT.QoL.Get("mapFogAlpha")) or 100) / 100 or 0
  for _, p in ipairs(z.pieces) do
    local a = z.explored[p.key] and 1 or fog
    for _, t in ipairs(p.tex) do
      if a > 0 then t:SetAlpha(a); t:Show() else t:Hide() end
    end
  end
end

local function hideZone(z)
  if not z.shown then return end
  z.shown = false
  for _, t in ipairs(z.tex or {}) do t:Hide() end
end
local function showZone(z)
  if z.shown then return end
  buildZone(z)
  z.shown = true
  for _, t in ipairs(z.tex) do t:Show() end
  applyFog(z) -- (hides the pieces that stay hidden)
end

local function forgetZones()
  for _, c in pairs(continents) do
    if c then for _, z in ipairs(c.zones) do hideZone(z); z.tex = nil end end
  end
end

--------------------------------------------------------------------------------
-- The view
--------------------------------------------------------------------------------

-- the view: its centre on the continent (0..1) and its zoom (1: the continent fits)
local function view()
  return sc:GetCurrentScrollX() or 0.5, sc:GetCurrentScrollY() or 0.5, sc:GetCanvasScale() / fitScale()
end

-- puts the view at once (Blizzard's InstantPanAndZoom drifts the pan toward the old one)
local function setView(scale, x, y)
  sc.currentScale, sc.targetScale, sc.zoomTarget = scale, scale, scale
  sc.Child:SetScale(scale)
  sc:CalculateScrollExtents()
  x = clamp(x, sc.scrollXExtentsMin or 0, sc.scrollXExtentsMax or 1)
  y = clamp(y, sc.scrollYExtentsMin or 0, sc.scrollYExtentsMax or 1)
  sc.targetScrollX, sc.targetScrollY, sc.currentScrollX, sc.currentScrollY = x, y, x, y
  sc:SetNormalizedHorizontalScroll(x)
  sc:SetNormalizedVerticalScroll(y)
  map:OnCanvasScaleChanged()
  if sc.MarkAreaTriggersDirty then sc:MarkAreaTriggersDirty() end
  if sc.MarkViewRectDirty then sc:MarkViewRectDirty() end
end
local wideView -- below: setView with the zoom's pan room
local function showAt(u, v, zoom) setView(zoom * fitScale(), u, v) end

local function deepestZoom()
  local id = map:GetMapID()
  local c = continent(id) or worldOf(id)
  return c and c.deepest or 8
end
local function inCombat() return InCombatLockdown and InCombatLockdown() end

-- the cursor's offset from the view's centre, in view px (y down)
local function cursorOffset()
  local x, y = GetCursorPosition()
  local es = sc:GetEffectiveScale()
  return x / es - (sc:GetLeft() + sc:GetWidth() / 2), (sc:GetTop() - sc:GetHeight() / 2) - y / es
end
-- continent units (0..1) per view px at `zoom`
local function perPx(zoom)
  local W, H = canvasSize()
  local px = fitScale() * zoom
  return 1 / (W * px), 1 / (H * px)
end

-- which zones show, and how strongly, for the view
local function refreshArt()
  if not active then return end
  local c = continent(map:GetMapID())
  local u, v, zoom = view()
  local a = clamp((zoom - DETAIL_FROM) / (DETAIL_FULL - DETAIL_FROM), 0, 1)
  a = a * a * (3 - 2 * a)
  if a <= 0 or not c then
    baseFrame:Hide(); pieceFrame:Hide()
    return
  end
  baseFrame:SetAlpha(a); pieceFrame:SetAlpha(a)
  baseFrame:Show(); pieceFrame:Show()
  local hu, hv = sc:GetWidth() / 2, sc:GetHeight() / 2
  local pu, pv = perPx(zoom)
  hu, hv = hu * pu * (1 + 2 * CULL_MARGIN), hv * pv * (1 + 2 * CULL_MARGIN)
  for _, z in ipairs(c.zones) do
    if z.r < u - hu or z.l > u + hu or z.b < v - hv or z.t > v + hv then hideZone(z) else showZone(z) end
  end
end

-- The point the wheel zooms toward: the one under the cursor, kept while the mouse stays where it is (user
-- 14.11.: near an edge the view could not hold it under the cursor yet, the next notch took the sea there
-- instead). A mouse move, a drag or another map picks a new one.
local STILL_PX = 3
local anchor -- { u, v, sx, sy, mapID }
local function zoomAtCursor(factor)
  local u, v, zoom = view()
  local sx, sy = cursorOffset()
  local a = anchor
  if not (a and a.mapID == map:GetMapID() and math.abs(a.sx - sx) <= STILL_PX and math.abs(a.sy - sy) <= STILL_PX) then
    local pu, pv = perPx(zoom)
    a = { u = u + sx * pu, v = v + sy * pv, sx = sx, sy = sy, mapID = map:GetMapID() }
    anchor = a
  end
  local from = anim and anim.target or zoom
  local least = (worldAbove(map:GetMapID()) and not inCombat()) and 0.05 or 1 -- (the world takes over below 1)
  local target = clamp(from * factor, least, deepestZoom())
  anim = { u = a.u, v = a.v, sx = a.sx, sy = a.sy, target = target }
end

-- The hand-overs. A continent's art is its rectangle on the world map, so a view of the world at zoom z is the
-- continent's view at z * (its width on the world): the same place, the same size on screen.
local function handOver(toMap, a, cu, cv, zoom, au, av, target)
  map:SetMapID(toMap)
  if not active then anim = nil; return end
  wideView(cu, cv, zoom)
  anchor = { u = au, v = av, sx = a.sx, sy = a.sy, mapID = toMap }
  target = clamp(target, 1, deepestZoom())
  anim = { u = au, v = av, sx = a.sx, sy = a.sy, target = target, down = a.down }
  if math.abs(math.log(target / zoom)) < 0.003 then anim = nil end
end
-- world -> continent, once the continent the zoom goes toward fills the view
local function intoContinent(a, zoom)
  local w = worldOf(map:GetMapID())
  local c = w and continentAt(w, a.u, a.v)
  if not c or zoom * (c.r - c.l) < 1 or inCombat() then return false end
  local x, y = view()
  local k, kv = c.r - c.l, c.b - c.t
  handOver(c.mapID, a, (x - c.l) / k, (y - c.t) / kv, zoom * k, (a.u - c.l) / k, (a.v - c.t) / kv, a.target * k)
  return true
end
-- continent -> world, zoomed out past the whole continent
local function outToWorld(a)
  local w, c = worldAbove(map:GetMapID())
  if not w or inCombat() then return false end
  local x, y = view()
  local k, kv = c.r - c.l, c.b - c.t
  handOver(w.mapID, a, c.l + x * k, c.t + y * kv, 1 / k, c.l + a.u * k, c.t + a.v * kv, a.target / k)
  return true
end

-- the zoom at which a rectangle (0..1 on this map) just fits the view
local function fitZoomOf(l, r, t, b)
  local W, H = canvasSize()
  return math.min(sc:GetWidth() / ((r - l) * W), sc:GetHeight() / ((b - t) * H)) / fitScale()
end
-- the zone of a continent at (u, v): the smallest whose rectangle holds it
local function zoneAt(c, u, v)
  local best, area
  for _, z in ipairs(c.zones) do
    if u >= z.l and u <= z.r and v >= z.t and v <= z.b then
      local a = (z.r - z.l) * (z.b - z.t)
      if not best or a < area then best, area = z, a end
    end
  end
  return best
end
-- a click's glide from the view to (u, v) at `zoom`, as one zoom about a fixed point (OpenMap's GlideTo);
-- `after` runs when it arrives
local function glideTo(u, v, zoom, after)
  local u0, v0, z0 = view()
  anchor = nil
  anim = { mode = "glide", u0 = u0, v0 = v0, z0 = z0, u1 = u, v1 = v, z1 = clamp(zoom, 1, deepestZoom()), t = 0, after = after }
end
local function glide(a, elapsed)
  local info = sc.mouseButtonInfo and sc.mouseButtonInfo.LeftButton
  if info and info.down then anim = nil; return end -- grabbed: the glide stops where it is
  a.t = math.min(1, a.t + elapsed / GLIDE_TIME)
  local e = a.t * a.t * (3 - 2 * a.t)
  local zoom = math.exp(math.log(a.z0) + (math.log(a.z1) - math.log(a.z0)) * e)
  -- the centre moves with 1/zoom, which is what zooming about one fixed point looks like
  local w = math.abs(a.z1 - a.z0) < 1e-6 and e or (1 / a.z0 - 1 / zoom) / (1 / a.z0 - 1 / a.z1)
  wideView(a.u0 + (a.u1 - a.u0) * w, a.v0 + (a.v1 - a.v0) * w, zoom)
  if a.t >= 1 then
    anim = nil
    if a.after then a.after() end
  end
end

-- after Blizzard's own OnUpdate, so its panning never adds to ours
local function animate(_, elapsed)
  local a = anim
  if not a then return end
  if not active then anim = nil; return end
  if a.mode == "glide" then return glide(a, elapsed) end
  local _, _, z = view()
  local zoom = math.exp(math.log(z) + (math.log(a.target) - math.log(z)) * (1 - math.exp(-elapsed * ZOOM_RATE)))
  local done = math.abs(math.log(a.target / zoom)) < 0.003
  if done then zoom = a.target end
  -- out past the whole continent: on in the world map (or, without one, stop at the whole continent)
  if zoom <= 1 and a.target < 1 and continent(map:GetMapID()) then
    if z <= 1.0005 and outToWorld(a) then return end
    zoom = 1
    if z <= 1.0005 then a.target, done = 1, true end
  end
  local info = sc.mouseButtonInfo and sc.mouseButtonInfo.LeftButton
  local down = info and info.down
  if down then anchor = nil end
  if down and not a.down then
    -- grabbed mid-zoom: what's under the cursor now is what the cursor carries
    local u, v = view()
    local sx, sy = cursorOffset()
    local pu, pv = perPx(z)
    a.u, a.v, a.sx, a.sy = u + sx * pu, v + sy * pv, sx, sy
  elseif down then
    a.sx, a.sy = cursorOffset()
  end
  a.down = down
  local pu, pv = perPx(zoom)
  wideView(a.u - a.sx * pu, a.v - a.sy * pv, zoom)
  if done then anim = nil end
  if worldOf(map:GetMapID()) then intoContinent(a, zoom) end
end

--------------------------------------------------------------------------------
-- Hooks into Blizzard's map
--------------------------------------------------------------------------------

-- Pan room past the continent's edges (as OpenMap's Extents; Blizzard's own when not stitched): for a drag half
-- the view; while the wheel zooms (wide) as much as keeps the point under the cursor there, even at the
-- continent's edge with the cursor at the view's; and never less than where the view is now, so a drag after
-- such a zoom does not jump.
local SLACK = 0.5
local wide = false
local function range(half, slack)
  local lo, hi = half, 1 - half
  if lo > hi then lo, hi = 0.5, 0.5 end
  return lo - slack, hi + slack
end
local function extents(orig)
  return function(self, scale)
    if not active then return orig(self, scale) end
    local hw = self:NormalizeHorizontalSize(self:GetWidth() * 0.5 / scale)
    local hh = self:NormalizeVerticalSize(self:GetHeight() * 0.5 / scale)
    local k = wide and 2 or 2 * SLACK
    local minX, maxX = range(hw, hw * k)
    local minY, maxY = range(hh, hh * k)
    local x, y = self.currentScrollX, self.currentScrollY
    if x and y then minX, maxX, minY, maxY = math.min(minX, x), math.max(maxX, x), math.min(minY, y), math.max(maxY, y) end
    return minX, maxX, minY, maxY
  end
end

wideView = function(u, v, zoom)
  wide = true
  local ok, err = pcall(showAt, u, v, zoom)
  wide = false
  if not ok then error(err, 0) end
end

local hookHighlight -- below
local function attach()
  local mapID = map:GetMapID()
  active = (on() and mapID and (continent(mapID) or worldOf(mapID))) and true or false
  if active then
    hookHighlight()
    sc:SetMouseWheelZoomMode(MAP_CANVAS_MOUSE_WHEEL_ZOOM_BEHAVIOR_NONE)
    if sc.SetScalingMode then sc:SetScalingMode("SCALING_MODE_LINEAR") end
  else
    anim = nil
    baseFrame:Hide(); pieceFrame:Hide()
    if wheelMode then sc:SetMouseWheelZoomMode(wheelMode) end
    if scalingMode and sc.SetScalingMode then sc:SetScalingMode(scalingMode) end
  end
end

-- zoom levels from the whole continent to DEEPEST screen px per zone map px
local function onCreateZoomLevels(self)
  attach()
  if not active then return end
  local c = continent(map:GetMapID())
  local w = not c and worldOf(map:GetMapID())
  if w and not w.deepest then
    local most = 1
    for _, cont in ipairs(w.conts) do most = math.max(most, 1 / (cont.r - cont.l)) end
    w.deepest = most * ZOOM_STEP
  end
  c = c or w
  if not c.deepest then
    local W = canvasSize()
    local list = {}
    for _, z in ipairs(c.zones) do list[#list + 1] = z.layer.layerWidth / ((z.r - z.l) * W) end
    table.sort(list)
    c.deepest = math.max(4, DEEPEST * list[math.ceil(#list / 2)] / fitScale())
  end
  local levels, zoom, fit = {}, 1, fitScale()
  while zoom < c.deepest * ZOOM_STEP do
    levels[#levels + 1] = { scale = math.min(zoom, c.deepest) * fit, layerIndex = 1 }
    zoom = zoom * ZOOM_STEP
  end
  self.zoomLevels = levels
  self.baseScale = levels[1].scale
end

-- after Blizzard's zoom reset (each map change and opening): framed on the zone the redirect came from
local function onResetZoom()
  if not active then return end
  local f = focus
  if f and f.mapID == map:GetMapID() and f.at == GetTime() then
    local W, H = canvasSize()
    local zoom = math.min(sc:GetWidth() / ((f.r - f.l) * W), sc:GetHeight() / ((f.b - f.t) * H)) / fitScale()
    showAt((f.l + f.r) / 2, (f.t + f.b) / 2, clamp(zoom * 0.95, 1, deepestZoom()))
  end
  refreshArt()
end

-- a zone map the game opens (the map opening on your zone, a quest, OneForAll's own buttons) shows as its
-- continent, framed on the zone. Not in combat: Blizzard's map isn't switched then
local redirecting = false
local function onMapChanged()
  local mapID = map:GetMapID()
  if not redirecting and on() and not (InCombatLockdown and InCombatLockdown()) then
    local c, z = continentOf(mapID)
    if c then
      focus = { mapID = c.mapID, l = z.l, r = z.r, t = z.t, b = z.b, at = GetTime() }
      redirecting = true
      local ok, err = pcall(map.SetMapID, map, c.mapID)
      redirecting = false
      if not ok then error(err, 0) end
      onResetZoom()
      return
    end
  end
  attach()
  refreshArt()
end

-- the wheel: a step toward the point under the cursor (the world and continents hand over in animate)
local function onMouseWheel(_, delta)
  if active then zoomAtCursor(delta > 0 and ZOOM_STEP or 1 / ZOOM_STEP) end
end

-- clicks on the stitched map do nothing (no zone in, no map out); a drag still moves the map
local function onCanvasClick(_, button)
  if not active or (button ~= "LeftButton" and button ~= "RightButton") then return false end
  local u, v, zoom = view()
  local sx, sy = cursorOffset()
  local pu, pv = perPx(zoom)
  local cu, cv = u + sx * pu, v + sy * pv
  local id = map:GetMapID()
  local c = continent(id)
  if button == "LeftButton" then
    if c then
      -- into the zone under the cursor
      local z = zoneAt(c, cu, cv)
      local fit = z and fitZoomOf(z.l, z.r, z.t, z.b) * 0.95
      if fit and fit > zoom * 1.05 then glideTo((z.l + z.r) / 2, (z.t + z.b) / 2, fit) end
    else
      -- the world: into the continent under the cursor, handed over to it where it fills the view
      local w = worldOf(id)
      local ct = w and continentAt(w, cu, cv)
      if ct and not inCombat() then
        local k, kv = ct.r - ct.l, ct.b - ct.t
        glideTo((ct.l + ct.r) / 2, (ct.t + ct.b) / 2, 1 / k, function()
          local x, y, zw = view()
          handOver(ct.mapID, { sx = 0, sy = 0 }, (x - ct.l) / k, (y - ct.t) / kv, zw * k, 0.5, 0.5, zw * k)
        end)
      end
    end
  elseif c and zoom > 1.01 then
    glideTo(0.5, 0.5, 1) -- out to the whole continent
  elseif c then
    -- the whole continent: handed over to the world, then out to the whole world
    local w, ct = worldAbove(id)
    if w and not inCombat() then
      local k, kv = ct.r - ct.l, ct.b - ct.t
      map:SetMapID(w.mapID)
      if active then
        wideView(ct.l + u * k, ct.t + v * kv, zoom / k)
        glideTo(0.5, 0.5, 1)
      end
    end
  elseif zoom > 1.01 then
    glideTo(0.5, 0.5, 1) -- the whole world
  end
  return true
end

-- Blizzard's zone highlight under the cursor is the continent's low detail art: away once the zones show
hookHighlight = function()
  for pin in map:EnumeratePinsByTemplate("MapHighlightPinTemplate") do
    if not pin.ofaSeamless and pin.Refresh and pin.HighlightTexture then
      pin.ofaSeamless = true
      hooksecurefunc(pin, "Refresh", function(self)
        if active and select(3, view()) >= DETAIL_FROM then self.HighlightTexture:Hide() end
      end)
    end
  end
end

local ready = false
local function setup()
  if ready then return true end
  map = _G.WorldMapFrame
  sc = map and map.ScrollContainer
  if not (sc and sc.CreateZoomLevels and sc.ResetZoom and sc.SetMouseWheelZoomMode and map.GetPinFrameLevelsManager
    and map.AddCanvasClickHandler and C_Map and C_Map.GetMapRectOnMap and C_Map.GetMapChildrenInfo and Enum and Enum.UIMapType) then
    return false
  end
  ready = true
  wheelMode = sc.mouseWheelZoomMode or MAP_CANVAS_MOUSE_WHEEL_ZOOM_BEHAVIOR_FULL
  scalingMode = sc.scalingMode
  -- the art just above Blizzard's own art and explored areas, under every icon
  local fl = map:GetPinFrameLevelsManager()
  pcall(fl.InsertFrameLevelAbove, fl, "PIN_FRAME_LEVEL_OFA_SEAMLESS", "PIN_FRAME_LEVEL_MAP_EXPLORATION", 2)
  local ok, level = pcall(fl.GetValidFrameLevel, fl, "PIN_FRAME_LEVEL_OFA_SEAMLESS")
  if not ok or type(level) ~= "number" then level = (map:GetCanvas():GetFrameLevel() or 1) + 2 end
  local canvas = map:GetCanvas()
  baseFrame = CreateFrame("Frame", nil, canvas)
  baseFrame:SetAllPoints(canvas); baseFrame:SetFrameLevel(level); baseFrame:Hide()
  pieceFrame = CreateFrame("Frame", nil, canvas)
  pieceFrame:SetAllPoints(canvas); pieceFrame:SetFrameLevel(level + 1); pieceFrame:Hide()

  if sc.CalculateScrollExtentsAtScale and sc.NormalizeHorizontalSize then
    sc.CalculateScrollExtentsAtScale = extents(sc.CalculateScrollExtentsAtScale)
  end
  hooksecurefunc(sc, "CreateZoomLevels", function(self) FLT.SafeCall("SeamlessMap", onCreateZoomLevels, self) end)
  hooksecurefunc(sc, "ResetZoom", function() FLT.SafeCall("SeamlessMap", onResetZoom) end)
  hooksecurefunc(map, "OnMapChanged", function() FLT.SafeCall("SeamlessMap", onMapChanged) end)
  sc:HookScript("OnMouseWheel", function(_, delta) FLT.SafeCall("SeamlessMap", onMouseWheel, nil, delta) end)
  sc:HookScript("OnUpdate", function(_, elapsed) if anim then FLT.SafeCall("SeamlessMap", animate, nil, elapsed) end end)
  map:AddCanvasClickHandler(onCanvasClick, 1000)
  if map.OnCanvasScaleChanged then hooksecurefunc(map, "OnCanvasScaleChanged", function() FLT.SafeCall("SeamlessMap", refreshArt) end) end
  if map.OnCanvasPanChanged then hooksecurefunc(map, "OnCanvasPanChanged", function() FLT.SafeCall("SeamlessMap", refreshArt) end) end
  hookHighlight()
  return true
end

-- the option switched (QoL.lua) or the map opened: lay the map out again
function SM.Refresh()
  if not setup() then return end
  if not map:IsShown() then attach(); return end
  if not on() then
    if active then
      active = false
      attach()
      sc:CreateZoomLevels() -- Blizzard's own zoom levels again
      sc:ResetZoom()
    end
    return
  end
  local mapID = map:GetMapID()
  if mapID and continentOf(mapID) then onMapChanged(); return end -- a zone: shown as its continent
  sc:CreateZoomLevels() -- ours (onCreateZoomLevels)
  sc:ResetZoom()
end

-- Remove Fog or its slider changed (QoL.lua), or you explored somewhere (below): the zones shown again
function SM.RefreshFog(explored)
  for _, c in pairs(continents) do
    if c then
      for _, z in ipairs(c.zones) do
        if explored then z.explored = nil end
        if z.shown then applyFog(z) end
      end
    end
  end
end

-- /ofa seamlessbase: the zones' base maps on or off, to compare the look (test builds)
function SM.ToggleBase()
  showBase = not showBase
  forgetZones()
  if FLT.Msg then FLT.Msg("Seamless map: zone base maps " .. (showBase and "on" or "off")) end
  if active then refreshArt() end
end

local f = CreateFrame("Frame")
f:RegisterEvent("PLAYER_LOGIN")
f:SetScript("OnEvent", function(self, event)
  if event == "MAP_EXPLORATION_UPDATED" then
    FLT.SafeCall("SeamlessMap", SM.RefreshFog, true)
    return
  end
  self:UnregisterEvent("PLAYER_LOGIN")
  self:RegisterEvent("MAP_EXPLORATION_UPDATED")
  FLT.SafeCall("SeamlessMap", setup)
end)
