( defun implication (e)
	(if(atom e) e
		(if (eq 1 (length e)) e
			; expression should of form A implies B
			; chage it t0- (not A) or B
			;apply again recursively to A and B
			(if (equal 'implies (first (rest e)))
				(
					append ( list ( list 'NOT (implication (first e)))
							  'or
					   )
					   (cons (implication( first (rest (rest e)))) nil)
				)						
				; handling expressions with NOT
				(if (equal 'not (first e))
					(list 'not (implication (first (rest e))))
					;expression in neither of the above two forms
					; A op B form. So recurse on A and B
					(list (implication (first e)) 
						  (first (rest e)) 
						  (implication (first (rest (rest e)))))
				)
			)
		)	
	)
)

( defun equivalence (e)
	(if(atom e) e
		(if (eq 1 (length e)) e
			; handling A equivalent B form
			; change it to (Not A OR B) AND (A OR NOT B)
			; recurse again on the new formed sub expressions
			(if (equal 'equivalent (first (rest e)))
				(
					list ( equivalence (append (list (first e) 'implies)
											   ( rest (rest e))))
						 'and					   
						 (equivalence( append (append ( rest (rest e)) 
													  (cons 'implies nil))
											  (cons (first e) nil)))
				)			
				;handling not A form
				(if (equal 'not (first e))
					(list 'not (implication (first (rest e))))
					
					;expression in neither of the above forms
					;recurse on left and right of the expression
					(list (equivalence (first e)) 
						  (first (rest e)) 
						  (equivalence (first (rest (rest e)))))
				)
			)
		)	
	)
)

( defun deMorganNot (e)
	(if (atom e) e
		(if (eq 1 (length e)) e
			; Expression in (NOT A) form
			(if (equal 'not (first e))
				;Moving NOT inside to be applied only at literal level
				; base condition (NOT a) where 'a' is literal
				(cond ((atom (first(rest e)))
						e
					  )
					  ;(Not (Not A)) will give back  A
					  ; recurse on A to see what is the final resolution
					  ( (equal 'not (first(first (rest e))))
						(deMorganNot (first(rest (first (rest e)))))
					  )
					  ; Not (A and B) will give (NOT A or Not B)
					  ((equal 'and (first(rest(first(rest e)))))
					   (list (deMorganNot (list 'not (first(first(rest e))))) 
							 'or 
							 (deMorganNot (append (cons 'not nil)(rest(rest(first(rest e)))))))
					  )
					  ; Not (A or B) will give (NOT A And Not B)
					  ((equal 'or (first(rest(first(rest e)))))
					   (list (deMorganNot (list 'not (first(first(rest e)))))  
							 'and
							 (deMorganNot (append (cons 'not nil)(rest(rest(first(rest e)))))))
					  )
					  ; Some other operand, reject it
					  (t '(Unrecognized connective))
				)
				; List is not in (Not (A op B)) form. Check A and B for Not
				(
					list (deMorganNot (first e)) 
						 (first (rest e)) 
						 (deMorganNot (first (rest (rest e))))
				)
			)	
		)
	)
)

(defun exprToCNF (e)
	(if (or (atom e) (eq 2 (length e))) e
		(if (eq 1 (length e)) e
		; Expression should be of the form (A OR B)
		; where A and B can be literals or lists
		; (A AND B) type expressions are handled inside the else case
			(if (equal 'or (first (rest e)))
				;a or b. a or B. A or b. A or B  
				
				;a or b - both are literals 
				(cond ((and (or (atom (first e))(eq 2 (length (first e))))
							(or (atom (first(rest(rest e)))) (eq 2 (length (first(rest(rest e)))))))
							(list (first e)(first(rest(rest e)))) 
					  )
					  ;a or B
					  ((or (atom (first e)) (eq 2 (length (first e))))
					   ; B has an AND in it
					   ;expression is of form (a OR (C AND D))
					   (if (equal 'and (first(rest(first(rest(rest e))))))
						   (list (exprToCNF(list (first e)
										   'or 
										   (first(first(rest(rest e))))))
								 (exprToCNF(list (first e)
										   'or 
										   (first(rest(rest(first(rest(rest e))))))))
							)
							; B is of the form C OR D
							; hence original expression becomes a OR C OR D
							; check recursively for C and D
							(list (first e) 
								  (exprToCNF(first(first(rest(rest e)))))	
								  (exprToCNF(first(rest(rest(first(rest(rest e)))))))
						)
					   )
					  )
					  ;A or b
					  ((or (atom (first(rest(rest e)))) (eq 2 (length (first(rest(rest e))))))
		     		   (if(equal 'and (first(rest(first e))))
						   ; A has an AND in it 
						   ;expression is of form (a OR (C AND D))
						   (list (exprToCNF(list (first(first e))
												 'or 
												 (first(rest(rest e)))))
								 (exprToCNF(list (first(rest(rest(first e))))
									             'or 
									             (first(rest(rest e)))))
							)
							; A is of the form C OR D
							; hence original expression becomes C OR D OR b
							; check recursively for C and D 
							(list (exprToCNF(first(first e)))
								  (exprToCNF (first(rest(rest(first e)))))
								  (first(rest(rest e))) 
							)
						)	
					   )
					   ; Expression of the form (A and B) or C
					   ; apply demorgans , push the  OR, and remove the AND for simplification
					  ((equal 'and (first(rest(first e))))
					   (list (exprToCNF(list (first(first e))
											 'or 
											 (first(rest(rest e)))))
							 (exprToCNF(list (first(rest(rest(first e))))
											 'or 
											 (first(rest(rest e)))))
						)
					   )
					   ; Expression of the form A or (B and C)
					   ; apply demorgans , push the  OR, and remove the AND for simplification
					  ((equal 'and (first(rest(first(rest(rest e))))))
						(list (exprToCNF(list (first e)
											  'or 
											  (first(first(rest(rest e))))))
							  (exprToCNF(list (first e)
											  'or 
											  (first(rest(rest(first(rest(rest e))))))))
						)
					   )
					  (t 
					  ; if the neither of the above cases are true then the expression
					  ; is of the the form ((A or C) or (B or D))
					  (list (exprToCNF(first(first e)))
							(exprToCNF(first(rest(rest(first e)))))
							(exprToCNF(first(first(rest(rest e)))))
							(exprToCNF(first(rest(rest(first(rest(rest e)))))))
					  )
					  )
				)
				(
				; A AND B, drop the AND convert A and B to CNF respectively and merge 
				; If either of  A or B are atomic no need to process them
				; Recurse over A and B individually
					list ( if (atom (first e))
							   (cons (exprToCNF (first e)) nil)
							   (exprToCNF (first e))
						 )
						 ( if (atom (first (rest (rest e))))
							   (cons (exprToCNF (first (rest (rest e)))) nil)
							   (exprToCNF (first (rest (rest e))))
						 )
				)
			)	
		)
	)
)

( defun CNF (e)
;base conditions '(a)
	(if(and (eq 1 (length e))(atom (first e))) 
		(list e)
;base conditions '(not a)
		(if(and (eq 2 (length e))(atom(first (rest e))))
			(cons(list e) nil)
			; Call the previous define stages for the conversion
			(exprToCNF(deMorganNot(implication(equivalence e))))
		)
	)
)
