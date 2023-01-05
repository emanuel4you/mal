local M = {}

M.MalHashMap = {}
M.MalHashMap.__index = M.MalHashMap

function M.MalHashMap.new(...)
  arg = table.pack(...)
  if #arg % 2 ~= 0 then
    error("Hash map input must be even")
  end

  local self = {}
  setmetatable(self, M.MalHashMap)
  for i= 1, #arg, 2 do 
    self[arg[i]] = arg[i+1] 
  end

  return self
end

M.MalList = {}
M.MalList.__index = M.MalList

function M.MalList.new(lst)
  local self = lst and lst or {}
  setmetatable(self, M.MalList)
  return self
end

M.MalVector = {}
M.MalVector.__index = M.MalVector
function M.MalVector.new(lst)
  local self = lst and lst or {}
  setmetatable(self, M.MalVector)
  return self
end

M.Sym = {}
M.Sym.__index = M.Sym
function M.Sym.new(val)
  local self = {}
  self.val = val
  setmetatable(self, M.Sym)
  return self
end
M.Err = {}
M.Err.__index = M.Err
function M.Err.new(val)
  local self = {}
  self.val = val
  setmetatable(self, M.Err)
  return self
end




M.MalNilType = {}
M.MalNilType.__index = M.MalNilType
function M.MalNilType.new()
  local self = setmetatable({}, M.MalNilType)
  return self
end

function M.MalNilType:tostring()
  return "Nil"
end

M.Nil = M.MalNilType.new()


function M.isinstanceof(obj, super)
  local mt = getmetatable(obj)
  while true do 
    if mt == nil then return false end
    if mt == super then return true end
    mt = getmetatable(mt)
  end
end

return M
