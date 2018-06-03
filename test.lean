universe u

namespace hide

-- BEGIN
inductive list (α : Type u) 
| nil {} : list
| cons : α → list → list

namespace list

notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

section
  open nat
  #check [1, 2, 3, 4, 5]
  #check ([1, 2, 3, 4, 5] : list int)
  #check @nil
end

end list
-- END

end hide