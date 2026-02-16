(declare-const x Int)
(declare-const result Int)

; The addOne function test

; Precondition: x > 0
(assert (> x 0))

; Function behavior: result = x + 1
(assert (= result (+ x 1)))

; OPPOSITE OF postcondition: ! (result > 0)
(assert (not (> result 0)))

; check if allowed
(check-sat)

; unsat = impossible for result to not be bigger than 0
; so negate postcondition , check-sat->(unsat) means normal postcondition-> always sat

; sat, always trying to find atleast 1 case where somethings working
; unsat !postcondtition, i cant find 1 case where the postconditions wrong