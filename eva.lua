local re = require're'
local i = require'inspect'

require 'lpeg'

function foldl(initial, fun, t)
  local accum = initial
  for i,v in ipairs(t) do
    accum = fun(accum, v)
  end
  return accum
end

function map(fun, t)
  local f = function(acc, x)
    table.insert(acc, fun(x))
    return acc
  end
  local init = {}
  return foldl(init, f,  t)
end

function each(fun, t)
  local f = function(_, x)
    fun(x)
  end
  return foldl({}, f, t)
end

-- local function map(fun, t)
--   local res = {}
--   for k, v in ipairs(t) do
--     res[#res+1] = fun(v)
--   end
--   return res
-- end

-- local function each(fun, t)
--   for k,v in ipairs(t) do
--     fun(v)
--   end
-- end

local inspect
local printers = {
  ['function'] = function(x) return '<function>'  end,
  list = function(x)
    local b = {}
    table.insert(b, '(')
    each(function(y)
           table.insert(b, inspect(y))
           table.insert(b, ' ')
         end, x)
    table.insert(b, ') ')
    return table.concat(b)
  end,
  number = tostring,
  string = tostring,
}

local function typeof(x)
  local object_type
  if type(x) == 'table' and getmetatable(x) then
    object_type =  getmetatable(x).class
  elseif type(x) == 'table' then
    object_type = 'list'
  else
    object_type = type(x)
  end
  return object_type
end

inspect = function(x)
  local object_type = typeof(x)
  if printers[object_type] then
    return printers[object_type](x)
  end
end

local pinspect = function(x) print(inspect(x)) end

local function import(lib, ...)
  each(function(x) _G[x] = lib[x] end, {...})
end

import(lpeg, "match", "P", "S", "R")

local Env = {}
function Env.new(parent)
  return {parent = parent}
end

local eval
local Fun = {}
function Fun.new(params,code, env)
  local o =  {
    params = params,
    code = code,
    env = env
  }
  return setmetatable(o,{class = 'function',
                        __call = function(_,...)
                           for i,v in ipairs({...}) do
                             o.env[o.params[i]] = v -- FIXME: o.env
                                                   -- will be reused
                                                   -- along calls, and
                                                   -- if the lambda is
                                                   -- called without
                                                   -- params the
                                                   -- second time,
                                                   -- we'll reuse
                                                   -- previous
                           end
                           return eval(o.code , o.env)
                     end})
end

local builtins = {
  ['+'] = function( ... )
      local r = 0
      for _,i in ipairs({...}) do
        r = r+i
      end
      return r
    end,
  ['<'] = function(x,y) return x<y end,
  ['>'] = function(x,y) return x>y end,
  ['='] = function(x,y) return x == y end,
  ['or'] = function(x,y) return x or y end,
  ['not'] = function(x) return not x end,
  ['and'] = function(x,y) return x and y end,
  ['-'] = function(x,y,...)
      if not y then return  0 - x end
      local r = x-y
      for _,i in ipairs({...}) do
        r = r - i
      end
      return r
    end
}

local Root = Env.new(builtins)

local P = [[
S <- <atom> / '(' %s* <S>* -> {} ')' %s*
atom <- { number / symbol } %s*
number <- '-' [0-9]+ / [0-9]+
symbol <- [!=<>a-zA-Z_+-]+ %s*
]]

local function head(t) return t[1] end

local function tail(t)
  local res = {}
  for i = 2, #t do
    res[i-1] = t[i]
  end
  return res
end

function lookup(str, env)
  str = str:gsub(" ", "")
  if env[str] then
    return env[str]
  else
    if not env.parent then error('nonexistant "' .. str ..'"') end
    return lookup(str, env.parent)
  end
end

function lookup_l(str, env)
  str = str:gsub(" ", "")
  if env[str] then
    return env
  else
    if not env.parent then error('nonexistant ' .. str) end
    return lookup_l(str, env.parent)
  end
end

local _if
local _lambda
local _define
local _set
local _begin

function eval(t, env)
  -- atom
  if type(t) ~= 'table' then
    if t:match("^-?%d+$") then return tonumber(t) end
    if t:match('^".+"$') then return t end
    if t:match('^.+$') then return lookup(t,env) end
  end

  -- special forms
  local h, ta = head(t), tail(t)
  if type(h) ~= 'table' then
    if h:match'lambda' then return _lambda (env, unpack(ta)) end
    if h:match'define' then return _define (env, unpack(ta)) end
    if h:match'if'     then return _if     (env, unpack(ta)) end
    if h:match'set!'   then return _set    (env, unpack(ta)) end
    if h:match'begin'  then return _begin  (env, unpack(ta)) end
  end

  -- normal application
  return eval(h, env)(unpack(map(function(x) return eval(x, env) end, ta)))
end

function _begin(env, ...)
  local x = {...}
  for i = 1, #x-1 do
    eval(x[i], env)
  end

  return eval(x[#x], env)
end

function _set(env, name, to)
  name = name:gsub(" ", "")
  local e = lookup_l(name, env)
  e[name] = eval(to, env)
  return e[name]
end

function _define(env, name, ...)
  if typeof(name) == 'list' then
    name[1] = name[1]:gsub(" ", "")
    pinspect(thing)
    env[name[1]] = _lambda(env, tail(name), ...)
    return env[name[1]]
  else
    name = name:gsub(" ", "")
    env[name] = eval(thing, env)
    return env[name]
  end
end

function _lambda(env, params, ...)
  local body = {...}
  if #body>1 then body = {'begin', unpack(body)} end
  print('lambda, ', i(body))
  return Fun.new(params, body, Env.new(env))
end

function _if(env, pred, yes, no)
  if eval(pred,env) then
    return eval(yes, env)
  else
    return no and eval(no, env) or nil
  end
end

while true do
  local line = io.read("*l")
  l = re.match(line,P)
  pinspect(eval(l, Root))
end
