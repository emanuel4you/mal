local M = {}

M.MalHashMap = {}
M.MalHashMap.__index = M.MalHashMap

function M.MalHashMap.new(...)
  arg = table.pack(...)
  if #arg % 2 ~= 0 then
    error("Hash map input must be even but got '" .. #arg .. "'")
  end

  local self = {}
  setmetatable(self, M.MalHashMap)
  for i= 1, #arg, 2 do 
    if M.isinstanceof(arg[i], M.Sym) and "\u{29E}" == string.sub(arg[i].val,1,2) then
      self[arg[i].val] = arg[i+1]
    else

      self[arg[i]] = arg[i+1] 
    end

  end

  return self
end

function M.MalHashMap:keys()
  local res = {}
  for k,_ in pairs(self) do
    table.insert(k)
  end
  return M.MalList.new(res)
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

function M.throw(val)
  error(M.Err.new(val))
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

M.MalFunction = {}
M.MalFunction.__index = M.MalFunction
function M.MalFunction.new(fn, ast, env, params, is_macro)
  local self = {fn = fn, ast = ast, env = env, params = params, is_macro = is_macro}
  return setmetatable(self, M.MalFunction)
end

function M.is_malfunc(a)
  return M.isinstanceof(a, M.MalFunction)
end

function M.is_func(a)
  return type(a) == "function" or (M.isinstanceof(a, M.MalFunction) and not a.is_macro)
    or M.isinstanceof(a, M.FunctionRef)
end


function M.is_sequence(a)
  return M.isinstanceof(a, M.MalList) or M.isinstanceof(a, M.MalVector)
end

M.Atom = {}
M.Atom.__index = M.Atom
function M.Atom.new(val)
  local self = {val = val}
  return setmetatable(self, M.Atom)
end

function M.is_atom(v)
  return M.isinstanceof(v, M.Atom)
end


function M.is_equal(a, b)
  if M.isinstanceof(a, M.Sym) and M.isinstanceof(b, M.Sym) then
    return a.val == b.val
  elseif M.is_sequence(a) and M.is_sequence(b) then
    if #a ~= #b then return false end
    for i,v in ipairs(a) do 
      if not M.is_equal(v, b[i]) then
        return false
      end end
    return true
  elseif M.isinstanceof(a, M.MalHashMap) and M.isinstanceof(b, M.MalHashMap) then
    for k,v in pairs(a) do
      if not ( M.is_equal(a[k],b[k])) then
        return false
      end
    end
    return true

  else 
    return a == b
  end

end



function M.isinstanceof(obj, super)
  local mt = getmetatable(obj)
  while true do 
    if mt == nil then return false end
    if mt == super then return true end
    mt = getmetatable(mt)
  end
end


function M.copy(obj)
    if type(obj) == "function" then
        return M.FunctionRef.new(obj)
    end
    if type(obj) ~= "table" then return obj end

    -- copy object data
    local new_obj = {}
    for k,v in pairs(obj) do
        new_obj[k] = v
    end

    -- copy metatable and link to original
    local old_mt = getmetatable(obj)
    if old_mt ~= nil then
        local new_mt = {}
        for k,v in pairs(old_mt) do
            new_mt[k] = v
        end
        setmetatable(new_mt, old_mt)
        setmetatable(new_obj, new_mt)
    end

    return new_obj
end

M.FunctionRef = {}
M.FunctionRef.__index = M.FunctionRef

function M.FunctionRef.new(fn)
	local self = {fn = fn}
	return setmetatable(self, M.FunctionRef)
end

function M.FunctionRef.__call(self, ...)
	return self.fn(...)
end


return M
