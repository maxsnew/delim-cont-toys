#lang racket/base

(require redex)

(define-language dcc
  (τ ::= Int
         (τ → τ / τ)
         (Kont τ τ))
  (e ::= v
         p
         (e e)
         (e + e)
         (callcc lam)
         (throw e to e))
  (p ::= (% τ e))
  (v ::= x
         lam
         integer
         (kont (hide-hole K)))
  (lam ::= (λ (x : τ / τ) e))
  (K ::= (K e)          (v K)
         (K + e)        (v + K)
         (throw K to e) (throw v to K)
         hole
         )
  (E ::= K
         (in-hole K (% τ E)))
  (x ::= variable-not-otherwise-mentioned)
  (Γ ::= · (x : τ Γ))
  )

(define-judgment-form dcc
  #:mode     (ptypes I I O)
  #:contract (ptypes Γ p τ)
  [(types Γ e τ τ)
   --------------------
   (ptypes Γ (% τ e) τ)])

(define-judgment-form dcc
  #:mode     (types I I O I)
  #:contract (types Γ e τ τ)
  [-----------------------
   (types Γ integer Int τ)]
  [(types (x : τ Γ) e                   τ_1             τ_3)
   --------------------------------------------------------
   (types Γ         (λ (x : τ / τ_3) e) (τ → τ_1 / τ_3) τ_2)]
  ;; TODO: variable lookup
  [(ktypes Γ K τ            τ_1)
   -----------------------------
   ( types Γ K (Kont τ τ_1) τ_2)]
  )

(define-judgment-form dcc
  #:mode     (ktypes I I I I)
  #:contract (ktypes Γ K τ τ)
  [-----------------------
   (ktypes Γ hole τ_1 τ_2)]

  [(ktypes Γ K (τ → τ_1 / τ_2) τ_2)
   ( types Γ e τ τ_2)
   ----------------------
   (ktypes Γ (K e) τ_1 τ_2)]

  [(types  Γ v     (τ → τ_1 / τ_2) τ_2)
   (ktypes Γ K     τ               τ_2)
   ------------------------------------
   (ktypes Γ (v K) τ_1             τ_2)]

  
  )
