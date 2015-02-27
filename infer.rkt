#lang racket

;; original version by Yin Wang
;; modified by KimmyLeo

(define fatal
  (lambda (who . args)
    (printf "~s: " who)
    (for-each display args)
    (newline)
    (error 'infer "")))

(struct const (obj))
(struct var (name))
(struct lam (var body))
(struct app (rator rand))

;; Type = Symbol | TVar | Arr
(struct type (main))
(struct tvar (name))
(struct arr (from to serial))

(define make-arrow
  (lambda (from to)
    (arr from to #f)))

(define parse
  (lambda (sexp)
    (match sexp
      [x #:when (or (number? x) (string? x) (boolean? x)) (const x)]
      [x #:when (symbol? x) (var x)]
      [(list 'lambda (list x) body) (lam x (parse body))]
      [(list e1 e2) (app (parse e1) (parse e2))])))

(define parse-type
  (lambda (t)
    (define parse1
      (lambda (t s)
        (match t
          [(list a '-> b)
           (let*-values ([(a^ s1) (parse1 a s)]
                         [(b^ s2) (parse1 b s1)])
             (values (make-arrow a^ b^) s2))]
          [x #:when (and (symbol? x)
                         (eq? #\t (string-ref (symbol->string x) 0)))
             (cond
               [(assq x s) (lambda (p) (values (cdr p) s))]
               [else (let ([tv (tvar x)])
                       (values tv (cons `(,x . ,tv) s)))])]
          [x (values x s)])))
    (let*-values ([(t^ _s) (parse1 t '())])
      t^)))

(define unparse
  (lambda (t)
    (cond
      [(type? t) (unparse (type-main t))]
      [(tvar? t) (tvar-name t)]
      [(arr? t)
       (let ([serial (arr-serial t)])
         (cond
           [(not serial)
            `(,(unparse (arr-from t)) -> ,(unparse (arr-to t)))]
           [else
            (let ([lb (string->symbol (string-append "%" (number->string serial)))])
              `(,lb ,(unparse (arr-from t)) -> ,(unparse (arr-to t))))]))]
      [(pair? t)
       (cons (unparse (car t)) (unparse (cdr t)))]
      [(const? t) (const-obj t)]
      [(var? t) (var-name t)]
      [(app? t)
       `(,(unparse (app-rator t)) ,(unparse (app-rand t)))]
      [(lam? t)
       `(lambda ,(unparse (lambda var t)) ,(unparse (lam-body t)))]
      [else t])))

(define s0 '())
(define ext-sub (lambda (x v s) `((,x . ,v) . ,s)))

(define env0
  `((add1 . ,(type (parse-type '(int -> int))))
    (* . ,(type (parse-type '(int -> (int -> int)))))
    (- . ,(type (parse-type '(int -> (int -> int)))))
    (+ . ,(type (parse-type '(int -> (int -> int)))))
    (reverse . ,(type (parse-type '(string -> string))))))

(define ext-env (lambda (x v s) `((,x . ,v) . ,s)))

;; lookup :: (Var * Env) -> Maybe Type
(define lookup
  (lambda (x env)
    (let ([slot (assq x env)])
      (cond
        [(not slot) #f]
        [else (cdr slot)]))))

;; walk :: (TVar * Subst) -> {TVar, Type}
(define walk
  (lambda (x s)
    (let ([slot (assq x s)])
      (cond
        [(not slot) x]
        [(tvar? (cdr slot)) (walk (cdr slot) s)]
        [else (cdr slot)]))))


;; unify :: (Term * Term * Subst) -> Subst
(define unify
  (lambda (u v s)
    (define onStack?
      (lambda (u v stk)
        (cond
          [(null? stk) #f]
          [else
           (let ([head (car stk)])
             (cond
               [(and (eq? u (car head)) (eq? v (cdr head))) #t]
               [(and (eq? v (car head)) (eq? u (cdr head))) #t]
               [else (onStack? u v (cdr stk))]))])))
    (define unify1
      (lambda (u v s stk)
        (let ([u (walk u s)] [v (walk v s)])
          (cond
            [(and (symbol? u) (symbol? v) (eq? u v)) s]
            [(and (tvar? u) (tvar? v) (eq? u v)) s]
            [(onStack? u v stk) s]
            [(tvar? u) (ext-sub u v s)]
            [(tvar? v) (ext-sub v u s)]
            [(and (arr? u) (arr? v))
             (let ((s^ (unify1 (arr-from u) (arr-from v) s (cons `(,u . ,v) stk))))
               (and s^ (unify1 (arr-to u) (arr-to v) s^ (cons `(,u . ,v) stk))))]
            [else #f]))))
    (unify1 u v s '())))

;; reify :: Term -> Subst -> Term
(define reify
  (lambda (x s)
    (define reify1
      (lambda (x n s stk occur)
        (define name
          (lambda (s n)
            (string->symbol
             (string-append s (number->string n)))))
        (define get-serial
          (lambda (x occur n)
            (let ([occur (reverse occur)])
              (cond
                [(null? occur) #f]
                [(eq? x (car occur)) n]
                [else (get-serial x (cdr occur) (add1 n))]))))
        (let ([x (walk x s)])
          (cond
            [(or (memq x stk) (memq x occur))
             (let ([serial (get-serial x occur 0)])
               (cond
                 [(not serial)
                  (values (name "!" (length occur)) n s (cons x occur))]
                 [else
                  (values (name "!" serial) n s occur)]))]
            [(symbol? x) (values x n s occur)]
            [(tvar? x)
             (let ([v* (name "t" n)])
               (values v* (add1 n) (ext-sub x v* s) occur))]
            [(arr? x)
             (let*-values
                 ([(u n1 s1 o1) (reify1 (arr-from x) n s (cons x stk) occur)]
                  [(v n2 s2 o2) (reify1 (arr-to x) n1 s1 (cons x stk) o1)]
                  [(serial) (get-serial x o2 0)])
               (values (arr u v serial) n2 s2 o2))]
            [else
             (fatal "[reify] Type contains illegal object: " x)]))))
    (let*-values ([(x^ _n _s _0) (reify1 x 0 s '() '())])
      x^)))

(define reify-type
  (lambda (x s)
    (cond
      [(type? x)
       (type (reify-type (type-main x) s))]
      [(null? x) '()]
      [(pair? x)
       (cons (reify-type (car x) s)
             (reify-type (cdr x) s))]
      [else (reify x s)])))

(define infer-type
  (lambda (exp)
    (define infer1
      (lambda (exp env s)
        (cond
          [(const? exp)
           (let ([x (const-obj exp)])
             (cond
               [(number? x) (values (type 'int) s)]
               [(string? x) (values (type 'string) s)]
               [(boolean? x) (values (type 'bool) s)]))]
          [(var? exp)
           (let* ([x (var-name exp)]
                  [t (lookup x env)])
             (cond
               [(not t)
                (fatal 'infer (format "unbound varialbe: ~s \n" x))]
               [else (values t s)]))]
          [(lam? exp)
           (let ([x (lam-var exp)]
                 [body (lam-body exp)])
             (let*-values ([(t1) (type (tvar x))]
                           [(env*) (ext-env x t1 env)]
                           [(t2 s^) (infer1 body env* s)])
               (let ([t1main (type-main t1)]
                     [t2main (type-main t2)])
                 (values (type (arr t1main t2main #f)) s^))))]
          [(app? exp)
           (let ([e1 (app-rator exp)]
                 [e2 (app-rand exp)])
             (let*-values ([(t1 s1) (infer1 e1 env s)]
                           [(t2 s2) (infer1 e2 env s1)]
                           [(tv3) (tvar 'tv3)]
                           [(tv4) (tvar 'tv4)]
                           [(s3) (unify (type-main t1) (arr tv3 tv4 #f) s2)])
                           (cond
                             [(not s3)
                              (let ([t* (reify (type-main t1) s1)])
                                (fatal 'infer
                                       "trying to apply no function: \n"
                                       " - term: " (unparse e1) "\n"
                                       " - type: " (unparse t*) ))]
                             [else
                              (let ([s4 (unify (type-main t2) tv3 s3)])
                                (cond
                                  [(not s4)
                                   (let ([t1* (reify (type-main t1) s3)]
                                         [tv3* (reify tv3 s3)]
                                         [t2* (reify (type-main t2) s3)])
                                     (fatal 'infer'
                                            "incompatible argument type: \n"
                                            " - function: " (unparse e1) "\n"
                                            " - function type: " (unparse t1*) "\n"
                                            " - expected type: " (unparse tv3*) "\n"
                                            " - argument type: " (unparse t2*) "\n"
                                            " - argument: " (unparse e2) ))]
                                  [else
                                   (values (type tv4) s4)]))])))])))
    (infer1 (parse exp) env0 s0)))

(define infer
  (lambda (exp)
    (let*-values ([(t^ s^) (infer-type exp)])
      (unparse (reify (type-main t^) s^)))))
