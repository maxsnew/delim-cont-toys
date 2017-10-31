#lang racket/base

(require redex)

(define-language dc
  (T ::= (K τ τ τ))
  (τ ::= Int
         (τ → τ τ τ)
         (∀ (α) T)
         α
         )
  (e ::= ;; later: nil (e :: e)
         ;;          (list-match e [nil e] [(x :: x) e]) 
         (ret v)
         (e + e)
         (if0 e e e)
         x
         (e e)
         (e {τ})
         ;; (fix e)
         p             ;; reset
         (shift lam τ)
         
         ;; delimited call/cc
         ;; (let/cc x in e) (throw e to e) ;; Uncomposable delimited continuations
         ;; (kont (hide-hole F))
         )
  (v ::= i 
         lam
         (Λ (α) e)
         ;; (kont F)
         ;; nil (v :: v)
         )
  (lam ::= (λ (x : τ → τ) e))
  (p ::= (% τ e))
  ;; reset-free context
  (K ::= (K + e) (v + K)
         (K e) (v K)
         (if0 K e e)
         (K {τ})
         hole)
  
  (E ::= K 
         (in-hole K P))
  (P ::= (% τ E))

  (i ::= integer)
  (α ::= variable-not-otherwise-mentioned)
  (x ::= variable-not-otherwise-mentioned))

(define-extended-language dc+Env dc
  (Γ ::= · (x : τ Γ))
  (Δ ::= · (α Δ)))

(define-judgment-form dc+Env
  #:mode     (ptypes I I I O)
  #:contract (ptypes Δ Γ e τ)
  [--------------------
   (ptypes Δ Γ i Int)]
  
  [--------------------
   (ptypes Δ (x : τ Γ) x τ)]
  
  [(ptypes Δ Γ x τ)
   (side-condition (diff-var x x_2))
   ----------------------------
   (ptypes Δ (x_2 : τ_2 Γ) x τ)]
  
  [(types Δ (x : τ_1 Γ) e τ_2 τ_3 τ)
   -----------------------------------
   (ptypes Δ Γ (λ (x : τ_1 → τ_2) e) (τ_1 → τ_2 τ_3 τ))]
  
  [(types Δ Γ e τ τ_1 τ_1)
   --------------------------
   (ptypes Δ Γ (% e) τ)]
  ;; TODO: Λ rule
  )

;; conjecture: make final answer type input, other 2 types output
(define-judgment-form dc+Env
  #:mode     (types I I I I O O)
  #:contract (types Δ Γ e τ τ τ)
  
  
  [(types Δ Γ e_1 τ_1 τ_2 Int)
   (types Δ Γ e_2 τ_2 τ_3 Int)
   ---------------------------------------
   (types Δ Γ (e_1 + e_2) τ_1 τ_3 Int)]
  
  [(types Δ Γ e_1 τ_1 τ_2 Int)
   (types Δ Γ e_2 τ_2 τ_3 τ)
   (types Δ Γ e_3 τ_2 τ_3 τ)   
   ---------------------------------------------
   (types Δ Γ (if0 e_1 e_2 e_3) τ_1  τ_3  τ)]
  
  
  [(types Δ Γ e_1 τ_2 τ_3 (τ_1 → τ_4 τ_5 τ))
   (types Δ Γ e_2 τ_3 τ_4 τ_1)
   --------------------------------------
   (types Δ Γ (e_1 e_2) τ_2 τ_5 τ)]

  [(types Δ (x (∀ (α) (τ → α α τ_1)) : Γ) e τ_2 τ_3 τ_3)
   -------------------------------------------------------------------
   (types Δ Γ (shift (λ (x : (∀ (α) (τ → α α τ_1)) → τ_2) e)) τ_2 τ_1 τ)]
  
  [(types Δ Γ e τ_1
                (tsubst α τ τ_2)
                (∀ (α)
                   (K τ_2
                      τ_3
                      τ_1)))
   ----------------------------------------
   (types Δ Γ (e {τ}) τ_1
                      (tsubst α τ τ_3)
                      (tsubst α τ τ_1))]


  [(ptypes Δ Γ e τ)
   ----------------------------------
   (types  Δ Γ (ret e) τ_1 τ_1 τ)]
  )
  

(define-judgment-form dc+Env
  #:mode     (closed-type I I)
  #:contract (closed-type Δ τ)
  [-------------------
   (closed-type Δ Int)]
  [(closed-type Δ τ_1)
   (closed-type Δ τ_2)
   (closed-type Δ τ_3)
   (closed-type Δ τ_4)
   ---------------------------------------
   (closed-type Δ (τ_1 / τ_3 → τ_2 / τ_4))]
  [(closed-type Δ α)
   (side-condition (diff-tvar α_1 α))
   -----------------------
   (closed-type (α_1 Δ) α)]
  [---------------------
   (closed-type (α Δ) α)]
  [(closed-type (α Δ) τ)
   -------------------------
   (closed-type Δ (∀ (α) τ))])

(define-metafunction dc
  [(diff-tvar α_1 α_1) #f]
  [(diff-tvar α_1 α_2) #t])

(define-metafunction dc
  [(diff-var x_1 x_1) #f]
  [(diff-var x_1 x_2) #t])

(define-metafunction dc
  tsubst : α τ τ -> τ
  [(tsubst α τ Int) Int]
  [(tsubst α τ (τ_1 / τ_2 → τ_3 / τ_4))
   ((tsubst α τ τ_1) / (tsubst α τ τ_2)
                     → 
    (tsubst α τ τ_3) / (tsubst α τ τ_4))]
  [(tsubst α τ α)     τ]
  [(tsubst α τ α_1) α_1]
  
  [(tsubst α τ (∀ (α) τ_1)) (∀ (α) τ_1)]
  [(tsubst α τ (∀ (α_1) τ_1)) (∀ (α_1) (tsubst α τ τ_1))])
#;#;
(define-metafunction delim-cont
  Plus : i i -> i
  [(Plus i_1 i_2)
   ,(+ (term i_1) (term i_2))]
  )

(define-metafunction delim-cont
  subst : x e e -> e
  [(subst x_1 e x_1) e]
  [(subst x_1 e x_2) x_2]
  
  [(subst x e_3 i) i]
  
  [(subst x e_3 (e_1 + e_2))
   ((subst x e_3 e_1) + (subst x e_3 e_2))]
  
  [(subst x_1 e_3 (λ (x_1 : τ) e)) (λ (x_1 : τ) e)]
  [(subst x_1 e_3 (λ (x_2 : τ) e)) (λ (x_2 : τ) (subst x_1 e_3 e))]
  
  [(subst x e_4 (e_1 e_2))
   ((subst x e_4 e_1) (subst x e_4 e_2))]
  
  [(subst x e_1 (% τ_1 τ_2 e_2))
   (% τ_1 τ_2 (subst x e_1 e_2))]
  
  [(subst x_1 e_1 (shift (x_1) τ e_2))
   (shift (x_1) τ e_2)]
  [(subst x_1 e_1 (shift (x_2) τ e_2))
   (shift (x_2) τ (subst x_1 e_1 e_2))]
  
  [(subst x e_0 (if0 e_1 e_2 e_3))
   (if0 (subst x e_0 e_1)
        (subst x e_0 e_2)
        (subst x e_0 e_3))]
  
  [(subst x e_0 (Λ (α) e_1))
   (Λ (α) (subst x e_0 e_1))]
  
  [(subst x e_1 (e_2 {τ}))
   ((subst x e_1 e_2) {τ})])

(define red
  (reduction-relation dc
    #:domain p
    (--> (in-hole P (i_1 + i_2))
         (in-hole P (Plus i_1 i_2))
         "+")
    (--> (in-hole P ((λ (x : τ) e) v))
         (in-hole P (subst x v e))
         "β")
    (--> (in-hole P (if0 0 e_1 e_2))
         (in-hole P e_1)
         "if0-T")
    (--> (in-hole P (if0 i e_1 e_2))
         (in-hole P e_2)
         (side-condition (not (equal? 0 (term i))))
         "if0-F")
    (--> (in-hole P ((Λ (α) e) {τ}))
         (in-hole P e)
         "Λ-app")
    (--> (in-hole E (% τ_1 τ_2
                       (in-hole K (shift (x_1 : (∀ (α) (τ_5 / α -> τ_6 / α)))
                                         τ_3 τ_4
                                         e))))
         (in-hole E (% τ_1 τ_2 (subst x_1
                                      (Λ (α)
                                         (λ (x : τ_5)
                                           (% τ_3 τ_4 (in-hole K x)))) e)))
         (fresh x)
         "shift/reset")
    (--> (in-hole P (% τ v))
         (in-hole P v)
         "reset")
    ))

#|
(traces red (term ((λ (rev) (rev (1 :: (2 :: (3 :: nil)))))
                     ((λ (perv) (λ (l) (reset (perv l))))
                      (fix 
                       (λ (perv)
                         (λ (l)
                           (list-match l
                             [nil nil]
                             [(h :: t)
                              (shift k in (h :: (k (perv t))))]))))))))
(traces red 
  (term 
   ((λ (app) ((app (1 :: (2 :: (3 :: nil))))
              (4 :: (5 :: (6 :: nil)))))
    ((λ (papp) (λ (l1) (reset (papp l1))))
     (fix 
      (λ (papp)
        (λ (l1)
          (list-match l1
            [nil (shift k in k)]
            [(h :: t)
             (h :: (papp t))]))))))))
;; proof that this is shift and not control: the following should return 4
(traces red (term (reset ((shift k in (1 + (k 100))) + (shift k in 3)))))
;; (traces red (term (reset (1 + (let/cc k in (2 + (throw 3 to k)))))))

(define t (term 
 ((λ (ret)
    ((λ (put)
       ((λ (get)
          ((λ (seq)
             ((reset 
              ((seq (put 1))
                    ((λ (x)
                      ((seq (put (3 + x)))
                            (ret (x + (get 0)))))
                     (get 0))))
              0))
           (λ (e1)
              (λ (e2)
                ((λ (_)
                  e2)
                e1)))))
        (λ (x)
          (shift k in 
                 (λ (s)
                   ((k s) s))))))
     (λ (n)
       (shift k in (λ (s) ((k n) n)));; implement put
     )))
  (λ (a) 
    (λ (s) 
      a) ;; implement ret
  ))))
|#
#;
(apply-reduction-relation* red
 (term (% Int
          (3 + (shift (x:k : (∀ (t:α) (Int / t:α → Int / t:α)))
                 (((x:k {Int}) 3) + ((x:k {Int}) 4)))))))
