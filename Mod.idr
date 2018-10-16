%default total

-- The code --------------------------------------------------------------------

||| Unary division and modulus. If m = S pm, then qrk i Z Z pm pm = (q,r,k),
||| where q is the quotient i div m, r is the remainder r mod m, and k is the
||| complement of the remainder, such that r + k = pm (k is also counted down in
||| parallel with i in the algorithm, to keep track of when to adjust q and r).
||| If r + k = pm is true initially, it remains true on each iteration. The
||| value of i + q * m + r is also conserved on each iteration.
qrk: (i: Nat) -> (q: Nat) -> (r: Nat) -> (k: Nat) -> (pm: Nat) -> (Nat,Nat,Nat)
qrk Z q r k _ = (q,r,k)                          -- i zero:(q,r,k) is the result
qrk (S pi) q r Z pm = qrk pi (S q) Z pm pm -- k zero; reset k and r, increment q
qrk (S pi) q r (S pk) pm = qrk pi q (S r) pk pm       -- i, k down; r up; same q

||| qrk with the arguments required to compute (quotient,remainder,complement)
qrkz: (i: Nat) -> (pm: Nat) -> (Nat,Nat,Nat)
qrkz i pm = qrk i Z Z pm pm

||| Modulus (i `mod` m) by repeated subtraction (the standard library's
||| implementation of mod for Nat is not total!)
md: (i: Nat) -> (m: Nat) -> {auto mValid: m = S pm} -> Nat
md i _ {pm} = fst (snd (qrkz i pm))

||| Computes modular inverse of i from the result of qrkz i pm
invFromQrk: (Nat,Nat,Nat) -> Nat
invFromQrk (_,Z,_) = Z           -- r is zero, so i's inverse mod m is also zero
invFromQrk (_,_,k) = S k                          -- otherwise, it's m - r = S k

||| Modular inverse
modInv: (i: Nat) -> (m: Nat) -> {auto mValid: m = S pm} -> Nat
modInv i _ {pm} = invFromQrk (qrkz i pm)

||| Modular addition
modPlus: (i: Nat) -> (j: Nat) -> (m: Nat) -> {auto mValid: m = S pm} -> Nat
modPlus i j m = md (plus i j) m

-- Lemmas about equalities -----------------------------------------------------

||| Assigns the value e to a pattern p, generating an equality stating p = e
asEq: (e: t) -> (p : t ** p = e)
asEq e = (e ** Refl)

-- Lemmas about pairs ----------------------------------------------------------

||| Equality of a pair yields a pair of equalities (, is injective)
commaInj: p = (a,b) -> (a = fst p,b = snd p)
commaInj eq = rewrite eq in (Refl,Refl)

-- Arithmetic lemmas -----------------------------------------------------------

||| Adding something on the right can't make a thing smaller
ltePlusR: LTE a (plus a b)
ltePlusR {a = Z} = LTEZero
ltePlusR {a = S pa} = LTESucc (ltePlusR {a = pa})

||| Adding something on the left can't make a thing smaller
ltePlusL: LTE a (plus b a)
ltePlusL {a} {b} =
  let comm: (plus a b = plus b a) = plusCommutative a b
  in  rewrite sym comm in ltePlusR

||| If a + b = 0, then both a and b are zero
plusIsZero: plus a b = Z -> (a = Z, b = Z)
plusIsZero {a = Z} {b = Z} eq = (Refl, Refl)
plusIsZero {a = S _} eq = void (SIsNotZ eq)
plusIsZero {a} {b = S pb} eq =
  let comm: (plus (S pb) a = Z) = rewrite plusCommutative (S pb) a in eq
  in  void (SIsNotZ comm)

||| a + b - b = a
plusMinusRight: minus (plus a b) b = a
plusMinusRight {a} {b} =
  let comm: (plus a b = plus b a) = plusCommutative a b
      b0: (plus b Z = b) = plusZeroRightNeutral b
      cancel: (minus (plus b a) (plus b Z) = minus a Z) =
        plusMinusLeftCancel b a Z
      a0: (minus a Z = a) = minusZeroRight a
      cancel1: (minus (plus b a) (plus b Z) = minus (plus b a) b) =
        cong {f = \x => minus (plus b a) x} b0
  in  rewrite comm
      in  trans (sym cancel1) (trans cancel a0)

||| a + b - a = b
plusMinusLeft: minus (plus a b) a = b
plusMinusLeft {a} {b} =
  let comm: (plus a b = plus b a) = plusCommutative a b
  in  rewrite comm in plusMinusRight {a = b} {b = a}
  
||| If a + b = c, then b = c - a
plusRightMinus: plus a b = c -> b = minus c a
plusRightMinus plusEq = rewrite sym plusEq in sym plusMinusLeft

||| a + (S b) - (S c) = a + b - c
minusPlusSuccRightSucc: minus (plus a (S b)) (S c) = minus (plus a b) c
minusPlusSuccRightSucc {a} {b} {c} =
  let succPlus: (plus a (S b) = S (plus a b)) = sym (plusSuccRightSucc a b)
  in  rewrite succPlus in minusSuccSucc (plus a b) c

||| Rearrange (a + b) + (c + d) = (a + c) = (b + d)
crossPlus: plus (plus a b) (plus c d) = plus (plus a c) (plus b d)
crossPlus {a} {b} {c} {d} =
  let assoc1: (plus (plus a b) (plus c d) = plus (plus (plus a b) c) d) =
        plusAssociative (plus a b) c d
      assoc2: (plus (plus (plus a b) c) d = plus (plus a (plus b c)) d) =
        rewrite plusAssociative a b c in Refl
      comm: (plus (plus a (plus b c)) d = plus (plus a (plus c b)) d) =
        rewrite plusCommutative b c in Refl
      assoc3: (plus (plus a (plus c b)) d = plus (plus (plus a c) b) d) =
        rewrite plusAssociative a c b in Refl
      assoc4: (plus (plus (plus a c) b) d = plus (plus a c) (plus b d)) =
        sym (plusAssociative (plus a c) b d)
  in  trans assoc1 (trans assoc2 (trans comm (trans assoc3 assoc4)))

||| Proofs of LTE are unique
lteUniq: (p0: LTE a b) -> (p1: LTE a b) -> p0 = p1
lteUniq LTEZero LTEZero = Refl
lteUniq (LTESucc q0) (LTESucc q1) = cong $ lteUniq q0 q1

||| Proofs of LT are unique
ltUniq:  (p0: LT a b) -> (p1: LT a b) -> p0 = p1
ltUniq = lteUniq

-- Proofs about qrk (and qrkz) -------------------------------------------------

||| When qrk is given arguments where r + k = pm, it returns (q',r',k') where
||| r' + k' = pm
qrkRKok: plus r k = pm -> qrk i q r k pm = (q',r',k') -> plus r' k' = pm
qrkRKok {i = Z} rkOK eq =
  case eq of
    Refl => rkOK
qrkRKok {i = S pi} {q} {r} {k = Z} {pm} {q'} {r'} {k'} rkOK eq =
  let equiv: (qrk (S pi) q r Z pm = qrk pi (S q) Z pm pm) = Refl
      eq1: (qrk pi (S q) 0 pm pm = (q', r', k')) = trans (sym equiv) eq
      zeroPlus: (plus Z pm = pm) = Refl
  in  qrkRKok zeroPlus eq1
qrkRKok {i = S pi} {q} {r} {k = S pk} {pm} {q'} {r'} {k'} rkOK eq =
  let equiv: (qrk (S pi) q r (S pk) pm = qrk pi q (S r) pk pm) = Refl
      eq1: (qrk pi q (S r) pk pm = (q',r',k')) = trans (sym equiv) eq
      srpk: (plus (S r) pk = plus r (S pk)) = plusSuccRightSucc r pk
  in  qrkRKok (trans srpk rkOK) eq1
  
||| When qrk is given arguments where r + k = pm, it returns (q',r',k') where
||| q' * m + r' = i + q * m + r
qrkI:  
  plus r k = pm -> qrk i q r k pm = (q',r',k') ->
  plus (mult q' (S pm)) r' = plus i (plus (mult q (S pm)) r)
qrkI {i = Z} _ eq =
  case eq of
    Refl => Refl
qrkI {i = S pi} {q} {r} {k = Z} {pm} {q'} {r'} {k'} rkOK eq =
  let equiv: (qrk (S pi) q r Z pm = qrk pi (S q) Z pm pm) = Refl
      eq1: (qrk pi (S q) Z pm pm = (q', r', k')) = trans (sym equiv) eq
      zeroPlus: (plus Z pm = pm) = Refl
      recur: (plus (mult q' (S pm)) r' = plus pi (plus (mult (S q) (S pm)) Z)) =
        qrkI zeroPlus eq1
      dropZ:
          (plus pi (plus (mult (S q) (S pm)) Z) = plus pi (mult (S q) (S pm))) =
        rewrite plusZeroRightNeutral (mult (S q) (S pm)) in Refl
      redMul: (mult (S q) (S pm) = S (plus pm (mult q (S pm)))) = Refl
      plusMul: (plus pi (mult (S q) (S pm)) =
           plus pi (S (plus pm (mult q (S pm))))) =
        cong {f = \x => plus pi x} redMul
      succPlus:
          (S (plus pi (plus pm (mult q (S pm)))) =
            plus pi (S (plus pm (mult q (S pm))))) =
        plusSuccRightSucc pi _
      plusPM:
          (S (plus pi (plus pm (mult q (S pm)))) =
            S (plus pi (plus (mult q (S pm)) pm))) =
        rewrite plusCommutative pm (mult q (S pm)) in Refl
      rEqPm: (r = pm) = trans (sym (plusZeroRightNeutral r)) rkOK
  in  rewrite rEqPm
      in  trans recur
            (trans dropZ (trans plusMul (trans (sym succPlus) plusPM)))
qrkI {i = S pi} {q} {r} {k = S pk} {pm} {q'} {r'} {k'} rkOK eq =
  let equiv: (qrk (S pi) q r (S pk) pm = qrk pi q (S r) pk pm) = Refl
      eq1: (qrk pi q (S r) pk pm = (q',r',k')) = trans (sym equiv) eq
      srpk: (plus (S r) pk = plus r (S pk)) = plusSuccRightSucc r pk
      recur: (plus (mult q' (S pm)) r' = plus pi (plus (mult q (S pm)) (S r))) =
        qrkI (trans srpk rkOK) eq1
      sr: (plus pi (plus (mult q (S pm)) (S r)) =
          plus pi (plus (S (mult q (S pm))) r)) =
        cong {f = \x => plus pi x} (sym (plusSuccRightSucc (mult q (S pm)) r))
      sMul:
          (plus pi (S (plus (mult q (S pm)) r)) =
            S (plus pi (plus (mult q (S pm)) r))) =
        sym (plusSuccRightSucc pi _)
  in  trans recur (trans sr sMul)

||| i can be viewed as q * m + r, where m = S pm, and qrkz computes q and r
exQrkz: qrkz i pm = (q,r,k) -> i = plus (mult q (S pm)) r
exQrkz {i} {q} {r} {pm} eq =
  let qi = qrkI {i = i} {q = Z} {r = Z} {k = pm} {pm = pm} Refl eq
      plusZ: (plus (mult Z (S pm)) Z = mult Z (S pm)) =
        plusZeroRightNeutral (mult Z (S pm))
      multZ: (mult Z (S pm) = Z) = multZeroLeftZero (S pm)
      iPlusZ: (plus i (plus (mult Z (S pm)) Z) = plus i Z) =
        cong {f = \x => plus i x} (trans plusZ multZ)
      justI: (plus i Z = i) = plusZeroRightNeutral i
  in  sym (trans qi (trans iPlusZ justI))

||| A valid call to qrk always returns a remainder less than the modulus (S pm)
qrkValid: plus r k = pm -> LTE (fst (snd (qrk i q r k pm))) pm
qrkValid {i = Z} {q} {r} {k} {pm} rkOK =
  let ltep: LTE r (plus r k) = ltePlusR
  in  rewrite (sym rkOK) in ltep
qrkValid {i = S pi} {q} {r} {k = Z} {pm} rkOK =
  qrkValid {i = pi} {k = pm} {r = Z} Refl
qrkValid {i = S pi} {q} {r} {k = S pk} {pm} rkOK =
  let okOK: (plus (S pk) r = plus pk (S r)) = plusSuccRightSucc pk r
      comm: (plus r (S pk) = plus (S r) pk) =
        rewrite plusCommutative r (S pk)
        in  rewrite plusCommutative (S r) pk in
            okOK
  in  qrkValid {i = pi} {k = pk} {r = S r} (trans (sym comm) rkOK)

||| When i <= k, a valid call to qrk yields (q, i + r, k - i)
qrkLow: plus r k = pm -> LTE i k -> qrk i q r k pm = (q,plus i r,minus k i)
qrkLow {i = Z} {k} rkOK iLTEkpm = rewrite minusZeroRight k in Refl
qrkLow {i = S pi} {k = Z} rkOK iLTEkpm = void (succNotLTEzero iLTEkpm)
qrkLow {i = S pi} {q} {r} {k = S pk} {pm} rkOK iLTEkpm =
  let srpkRspk: (plus (S r) pk = plus r (S pk)) = plusSuccRightSucc r pk
      srpkOK: (plus (S r) pk = pm) = trans srpkRspk rkOK
      pisrSpir: (plus pi (S r) = plus (S pi) r) = sym (plusSuccRightSucc pi r)
      recur: (qrk pi q (S r) pk pm = (q,plus pi (S r),minus pk pi)) =
        qrkLow srpkOK (fromLteSucc iLTEkpm)
  in  rewrite sym pisrSpir in recur

||| When k < i <= m, a valid call to mdCmp yields (S q, i + r - m, m + k - i)
qrkHigh:
  plus r k = pm -> LTE (S k) i -> LTE i (S pm) ->
  qrk i q r k pm = (S q,minus (plus i r) (S pm),minus (plus (S pm) k) i)
qrkHigh {i = Z} _ kLTi _ = void (succNotLTEzero kLTi)
qrkHigh {i = S pi} {q} {r} {k = Z} {pm} rkOK kLTi iLTEm =
  let low: (qrk pi (S q) Z pm pm = (S q,plus pi Z,minus pm pi)) =
        qrkLow {i = pi} {k = pm} {r = Z} Refl (fromLteSucc iLTEm)
      rEqPm: (r = pm) = trans (sym (plusZeroRightNeutral r)) rkOK
      piz: (plus pi Z = pi) = plusZeroRightNeutral pi
      pirMinPm: (minus (plus pi r) pm = pi) =
        rewrite rEqPm in plusMinusRight
      pmz: (plus pm Z = pm) = plusZeroRightNeutral pm
  in  rewrite trans pirMinPm (sym piz)
      in  rewrite pmz
          in  low
qrkHigh {i = S pi} {q} {r} {k = S pk} {pm} rkOK kLTi iLTEm =
  let srpkOK: (plus (S r) pk = pm) = trans (plusSuccRightSucc r pk) rkOK
      recur:
          (qrk pi q (S r) pk pm =
            (S q,minus (plus pi (S r)) (S pm),minus (plus (S pm) pk) pi)) =
          qrkHigh {i = pi} {k = pk} {r = S r}
            srpkOK (fromLteSucc kLTi) (lteSuccLeft iLTEm)
      pirMinPm: (minus (plus pi (S r)) (S pm) = minus (plus pi r) pm) =
        minusPlusSuccRightSucc
      pmspk: (plus (S pm) pk = plus pm (S pk)) = plusSuccRightSucc pm pk
  in  rewrite sym pirMinPm
      in  rewrite sym pmspk
          in  recur

||| When k and r are valid, qrk with i = m adds one to the quotient
qrkM: plus r k = pm -> qrk (S pm) q r k pm = (S q,r,k)
qrkM {q} {r} {k = Z} {pm} rkOK =
  let low: (qrk pm (S q) Z pm pm = (S q,plus pm Z,minus pm pm)) =
        qrkLow {i = pm} {q = S q} {r = Z} {k = pm} Refl lteRefl
      pmZNeu: (plus pm Z = pm) = plusZeroRightNeutral pm
      minPmPm: (minus pm pm = Z) = sym (minusZeroN pm)
      tripleEq: ((S q,plus pm Z,minus pm pm) = (S q,pm,Z)) =
        rewrite pmZNeu in rewrite minPmPm in Refl
      rZNeu: (plus r Z = r) = plusZeroRightNeutral r
      rEqPm: (r = pm) = trans (sym rZNeu) rkOK
  in  rewrite rEqPm in trans low tripleEq
qrkM {q} {r} {k = S pk} {pm} rkOK =
  let srpk: (plus (S r) pk = pm) = trans (plusSuccRightSucc r pk) rkOK
      kLTEpm: LTE (S pk) pm = rewrite sym rkOK in ltePlusL
      hi: (qrk pm q (S r) pk pm =
          (S q,minus (plus pm (S r)) (S pm),minus (plus (S pm) pk) pm)) =
        qrkHigh {i = pm} {q = q} {r = S r} {k = pk}
          srpk kLTEpm (lteSuccRight lteRefl)
      minPmrPm: (minus (plus pm (S r)) (S pm) = minus (plus pm r) pm) =
        minusPlusSuccRightSucc
      minRpmPm: (minus (plus pm r) pm = minus (plus r pm) pm) =
        rewrite plusCommutative r pm in Refl
      eqR: (minus (plus r pm) pm = r) = plusMinusRight
      minPmSpk: (minus (plus (S pm) pk) pm = minus (plus pm (S pk)) pm) =
        rewrite plusSuccRightSucc pm pk in Refl
      minSpkPm: (minus (plus pm (S pk)) pm = minus (plus (S pk) pm) pm) =
        rewrite plusCommutative pm (S pk) in Refl
      eqSpk: (minus (plus (S pk) pm) pm = S pk) = plusMinusRight
      tripleEq:
          ((S q,minus (plus pm (S r)) (S pm),minus (plus (S pm) pk) pm) =
            (S q,r,S pk)) =
        rewrite trans minPmrPm (trans minRpmPm eqR)
        in  rewrite trans minPmSpk (trans minSpkPm eqSpk)
            in  Refl
  in  trans hi tripleEq

||| When r and k are valid, adding m to i increases the quotient by 1, leaving
||| the remainder unchanged
qrkPlusM:
  plus r k = pm -> qrk i q r k pm = (q',r',k') ->
  qrk (plus i (S pm)) q r k pm = (S q',r',k')
qrkPlusM {i = Z} {q} rkOK eq =
  case eq of
    Refl => qrkM {q = q} rkOK
qrkPlusM {i = S pi} {q} {r} {k = Z} {pm} rkOK eq =
  qrkPlusM {i = pi} {q = S q} {r = Z} {k = pm} Refl eq
qrkPlusM {i = S pi} {q} {r} {k = S pk} {pm} rkOK eq =
  let srpk: (plus (S r) pk = pm) = trans (plusSuccRightSucc r pk) rkOK
  in  qrkPlusM {i = pi} {q = q} {r = S r} {k = pk} srpk eq

||| When r and k are valid, adding n * m to i increases the quotient by n,
||| leaving the reaminder unchanged
qrkPlusNtimesM:
  plus r k = pm -> qrk i q r k pm = (q',r',k') ->
  qrk (plus i (mult n (S pm))) q r k pm = (plus n q',r',k')
qrkPlusNtimesM {i} {n = Z} _ eq = rewrite plusZeroRightNeutral i in eq
qrkPlusNtimesM {i} {q} {r} {k} {pm} {q'} {r'} {k'} {n = S pn} rkOK eq =
  let recur = qrkPlusNtimesM {i = i} {q = q} {r = r} {k = k} {n = pn} rkOK eq
      plusM =
        qrkPlusM {i = plus i (mult pn (S pm))} {q = q} {r = r} {k = k}
          rkOK recur
      assoc:
          (plus i (plus (mult pn (S pm)) (S pm)) =
            plus (plus i (mult pn (S pm))) (S pm)) =
        plusAssociative i (mult pn (S pm)) (S pm)
      comm: (plus (mult pn (S pm)) (S pm) = plus (S pm) (mult pn (S pm))) =
        plusCommutative (mult pn (S pm)) (S pm)
      cCong:
          (plus i (plus (mult pn (S pm)) (S pm)) =
            plus i (plus (S pm) (mult pn (S pm)))) =
        cong {f = \x => plus i x} comm
  in  rewrite sym (trans (sym assoc) cCong) in plusM

||| qrk applied to the remainder from a previous call to qrk gives the same
||| result as the previous call, except the quotient is zero
qrkzMd:
  qrkz i pm = (qi,ri,ki) ->
  qrkz ri pm = (Z,ri,ki)
qrkzMd {i} {qi} {ri} {ki} {pm} qrki =
  let riOK: (plus ri ki = pm) = qrkRKok Refl qrki
      riValid: (LTE ri pm) = rewrite sym riOK in ltePlusR {a = ri} {b = ki}
      riLow: (qrkz ri pm = (Z,plus ri Z,minus pm ri)) =
        qrkLow {i = ri} {q = Z} {r = Z} {k = pm} Refl riValid
      rRewrite: (plus ri Z = ri) = plusZeroRightNeutral ri
      kRewrite: (ki = minus pm ri) = plusRightMinus riOK
      rsltEq: ((Z,plus ri Z,minus pm ri) = (Z,ri,ki)) =
        rewrite rRewrite in rewrite kRewrite in Refl
  in  trans riLow rsltEq

||| qrkz (i + j) pm in terms of qrk i and qrk j. Using exQrkz and
||| qrkPlusNtimesM, can also be understood as
||| i + j = (qi + qj + qrirj) * m + rrirj, where i = qi * m + ri,
||| j = qj * m + rj, and ri + rj = qrirj * m + rrirj
qrkzPlus:
  qrkz i pm = (qi,ri,ki) ->
  qrkz j pm = (qj,rj,kj) ->
  qrkz (plus ri rj) pm = (qrirj,rrirj,krirj) ->
  qrkz (plus i j) pm = (plus (plus qi qj) qrirj,rrirj,krirj)
qrkzPlus {i} {j} {pm} {qi} {ri} {ki} {qj} {rj} {kj} {qrirj} {rrirj} {krirj}
    qrki qrkj qrkrirj =
  let iEq: (i = plus (mult qi (S pm)) ri) = exQrkz qrki
      jEq: (j = plus (mult qj (S pm)) rj) = exQrkz qrkj
      rirjEq: (plus ri rj = plus (mult qrirj (S pm)) rrirj) = exQrkz qrkrirj
      -- The next few steps show that i + j = rrirj + (qi + qj + qrirj) * m:
      plusIj:
          (plus i j =
            plus (plus (mult qi (S pm)) ri) (plus (mult qj (S pm)) rj)) =
        rewrite iEq in rewrite jEq in Refl
      cross:
          (plus (plus (mult qi (S pm)) ri) (plus (mult qj (S pm)) rj) =
            plus (plus (mult qi (S pm)) (mult qj (S pm))) (plus ri rj)) =
        crossPlus
      dist1:
          (plus (plus (mult qi (S pm)) (mult qj (S pm))) (plus ri rj) =
            plus (mult (plus qi qj) (S pm)) (plus ri rj)) =
          rewrite multDistributesOverPlusLeft qi qj (S pm) in Refl
      rirj:
          (plus (mult (plus qi qj) (S pm)) (plus ri rj) =
            plus (mult (plus qi qj) (S pm)) (plus (mult qrirj (S pm)) rrirj)) =
        rewrite rirjEq in Refl
      assoc:
          (plus (mult (plus qi qj) (S pm)) (plus (mult qrirj (S pm)) rrirj) =
            plus (plus (mult (plus qi qj) (S pm)) (mult qrirj (S pm))) rrirj) =
        rewrite
            plusAssociative (mult (plus qi qj) (S pm)) (mult qrirj (S pm)) rrirj
          in Refl
      dist2:
          (plus (plus (mult (plus qi qj) (S pm)) (mult qrirj (S pm))) rrirj =
            plus (mult (plus (plus qi qj) qrirj) (S pm)) rrirj) =
        rewrite multDistributesOverPlusLeft (plus qi qj) qrirj (S pm) in Refl
      comm:
          (plus (mult (plus (plus qi qj) qrirj) (S pm)) rrirj =
            plus rrirj (mult (plus (plus qi qj) qrirj) (S pm))) =
        plusCommutative (mult (plus (plus qi qj) qrirj) (S pm)) rrirj
      bigTrans:
          (plus i j = plus rrirj (mult (plus (plus qi qj) qrirj) (S pm))) =
        trans plusIj
          (trans cross
            (trans dist1 (trans rirj (trans assoc (trans dist2 comm)))))
      -- Now calculate qrk rrirj... for use in qrkPlusNtimesM {i = rrirj}...:
      rrirjMd: (qrkz rrirj pm = (Z,rrirj,krirj)) = qrkzMd qrkrirj
      -- use qrkPlusNtimesM to complete the formula:
      nTimes:
          (qrkz (plus rrirj (mult (plus (plus qi qj) qrirj) (S pm))) pm =
            (plus (plus (plus qi qj) qrirj) Z,rrirj,krirj)) =
        qrkPlusNtimesM
          {i = rrirj} {q = Z} {r = Z} {k = pm} {n = plus (plus qi qj) qrirj}
          Refl rrirjMd
      -- with a little rewriting:
      qRewrite: (plus (plus (plus qi qj) qrirj) Z = (plus (plus qi qj) qrirj)) =
        plusZeroRightNeutral (plus (plus qi qj) qrirj)
      rsltEq:
          ((plus (plus (plus qi qj) qrirj) Z,rrirj,krirj) =
            (plus (plus qi qj) qrirj,rrirj,krirj)) =
        rewrite qRewrite in Refl
  in  rewrite bigTrans in trans nTimes rsltEq

||| qrkz (i + (j mod m)) pm, per qrkzPlus
qrkzPlusMd:
  qrkz i pm = (qi,ri,ki) ->
  qrkz j pm = (qj,rj,kj) ->
  qrkz (plus ri rj) pm = (qrirj,rrirj,krirj) ->
  qrkz (plus i rj) pm = (plus qi qrirj,rrirj,krirj)
qrkzPlusMd {i} {j} {pm} {qi} {ri} {ki} {qj} {rj} {kj} {qrirj} {rrirj} {krirj}
    qrki qrkj qrkrirj =
  let qrkjMd: (qrkz rj pm = (Z,rj,kj)) = qrkzMd qrkj
      qrkzPlusrj: 
         (qrkz (plus i rj) pm = (plus (plus qi Z) qrirj,rrirj,krirj)) =
        qrkzPlus qrki qrkjMd qrkrirj
      rsltEq:
          ((plus (plus qi Z) qrirj,rrirj,krirj) = (plus qi qrirj,rrirj,krirj)) =
        rewrite plusZeroRightNeutral qi in Refl
  in  trans qrkzPlusrj rsltEq

-- Proofs about invFromQrk -----------------------------------------------------

||| i + modInv i m = n * m for some n
plusInvFromQrk: (n: Nat ** plus i (invFromQrk (qrkz i pm)) = mult n (S pm))
plusInvFromQrk {i} {pm} =
  let ((q,r,k) ** qrkziEq) = asEq (qrkz i pm)
      xq: (i = plus (mult q (S pm)) r) = exQrkz (sym qrkziEq)
      rkOK: (plus r k = pm) = qrkRKok Refl (sym qrkziEq)
  in  rewrite sym qrkziEq
      in  case r of
            Z =>
              let iNeut: (plus i Z = i) = plusZeroRightNeutral i
                  qmNeut: (plus (mult q (S pm)) Z = mult q (S pm)) =
                    plusZeroRightNeutral (mult q (S pm))
              in  (q ** trans iNeut (trans xq qmNeut))
            S pr =>
              let congSk:
                      (plus i (S k) =
                        plus (plus (mult q (S pm)) (S pr)) (S k)) =
                    cong {f = \x => plus x (S k)} xq
                  assoc:
                      (plus (mult q (S pm)) (plus (S pr) (S k)) =
                        plus (plus (mult q (S pm)) (S pr)) (S k)) =
                    plusAssociative (mult q (S pm)) (S pr) (S k)
                  sprk: (plus (S pr) k = plus pr (S k)) = plusSuccRightSucc pr k
                  sprskm: (plus (S pr) (S k) = S pm) =
                    cong {f = S} (trans (sym sprk) rkOK)
                  plusMult:
                      (plus (mult q (S pm)) (plus (S pr) (S k)) =
                        plus (mult q (S pm)) (S pm)) =
                    rewrite sprskm in Refl
                  comm:
                      (plus (mult q (S pm)) (S pm) =
                        plus (S pm) (mult q (S pm))) =
                    plusCommutative (mult q (S pm)) (S pm)
              in  (S q **
                    trans congSk (trans (sym assoc) (trans plusMult comm)))

-- Validity relative to a modulus ----------------------------------------------

||| Whether a number i is valid modulo m, that is, whether i < m
ValidMod: (i: Nat) -> (m: Nat) -> Type
ValidMod i m = LT i m

-- Proofs about md -------------------------------------------------------------

||| i md m is valid modulo m whenever m is a valid modulus
mdValid: {auto mValid: m = S pm} -> ValidMod (md i m {mValid = mValid}) m
mdValid {pm} {mValid = Refl} {i} =
  LTESucc (qrkValid {i = i} {q = Z} {r = Z} {k = pm} Refl)

||| If i is already valid mod m, then i mod m = i
validMdSame: {auto mValid: m = S pm} -> (iValid: ValidMod i m) -> md i m = i
validMdSame {m} {pm} {mValid} {i} iValid =
  case mValid of
    Refl =>
      let low: (qrkz i pm = (Z,plus i Z,minus pm i)) =
            qrkLow {i = i} {q = Z} {r = Z} {k = pm} Refl (fromLteSucc iValid)
          rEq: (md i (S pm) = plus i Z) = cong {f = \x => fst (snd x)} low
      in  trans rEq (plusZeroRightNeutral i)

||| md is idempotent (with respect to a fixed modulus m)
mdIdem: {auto mValid: m = S mm} -> md i m = md (md i m) m
mdIdem {i} {m} =
  let mdVal = mdValid {i = i} {m = m}
  in  sym (validMdSame {m = m} {i = md i m} mdVal)

-- Proofs about modInv and modPlus ---------------------------------------------

||| The result of modPlus is valid
modPlusValid:
  {auto mValid: m = S pm} -> ValidMod (modPlus i j m {mValid = mValid}) m
modPlusValid {i} {j} {pm} {mValid = Refl} =
  LTESucc (qrkValid {i = plus i j} {q = Z} {r = Z} {k = pm} {pm = pm} Refl)

||| The result of modInv is valid
modInvValid:
  {auto mValid: m = S pm} -> ValidMod (modInv i m {mValid = mValid}) m
modInvValid {i} {m} {pm} {mValid} =
  let ((q,r,k) ** qrkEq) = asEq (qrkz i pm)
      rkOK: (plus r k = pm) =
        qrkRKok {i = i} {q = Z} {r = Z} {k = pm} {pm = pm} Refl (sym qrkEq)
  in  case r of
        Z => rewrite mValid in rewrite sym qrkEq in LTESucc LTEZero
        S pr =>
          let rsk: (plus (S pr) k = plus pr (S k)) = plusSuccRightSucc pr k
              skLTEplus: LTE (S k) (plus pr (S k)) = ltePlusL
              lte1: LTE (S k) pm = rewrite trans (sym rkOK) rsk in skLTEplus
          in  rewrite mValid in rewrite sym qrkEq in LTESucc lte1

||| modInv is an inverse for modPlus
modInvInverse: {auto mValid: m = S pm} -> modPlus i (modInv i m) m = Z
modInvInverse {i} {pm} =
  let (n ** plusiInvEq) = plusInvFromQrk {i = i} {pm = pm}
      qrkZEq: (qrkz Z pm = (Z,Z,pm)) = Refl
      nTimes: (qrkz (mult n (S pm)) pm = (plus n Z,Z,pm)) =
        qrkPlusNtimesM {i = Z} {q = Z} {r = Z} {k = pm} Refl qrkZEq
      plusI: (qrkz (plus i (invFromQrk (qrkz i pm))) pm = (plus n Z,Z,pm)) =
        trans (cong {f = \x => qrkz x pm} plusiInvEq) nTimes
  in  cong {f = \x => fst (snd x)} plusI

||| modPlus is commutative
modPlusComm: {auto mValid: m = S pm} -> modPlus i j m = modPlus j i m
modPlusComm {i} {j} =
  let comm: (plus i j = plus j i) = plusCommutative _ _
  in  rewrite comm in Refl

||| If you take an addend modulo m, you get the same result from modPlus
modPlusMod: {auto mValid: m = S pm} -> modPlus i j m = modPlus (md i m) j m
modPlusMod {i} {j} {pm} =
  let ((qi,ri,ki) ** iEq) = asEq (qrkz i pm)
      ((qj,rj,kj) ** jEq) = asEq (qrkz j pm)
      ((qrirj,rrirj,krirj) ** rirjEq) = asEq (qrkz (plus ri rj) pm)
      qrkzPlusIj: (qrkz (plus i j) pm = (plus (plus qi qj) qrirj,rrirj,krirj)) =
        qrkzPlus (sym iEq) (sym jEq) (sym rirjEq)
      commRiRj: (qrkz (plus ri rj) pm = qrkz (plus rj ri) pm) =
        rewrite plusCommutative ri rj in Refl
      qrkzPlusJRi: (qrkz (plus j ri) pm = (plus qj qrirj,rrirj,krirj)) =
        qrkzPlusMd (sym jEq) (sym iEq) (trans (sym commRiRj) (sym rirjEq))
      commRij: (qrkz (plus ri j) pm = qrkz (plus j ri) pm) =
        rewrite plusCommutative ri j in Refl
  in  rewrite sym iEq
      in  rewrite trans commRij qrkzPlusJRi
          in  rewrite qrkzPlusIj
              in  Refl

||| modPlus is associative
modPlusAssoc:
  {auto mValid: m = S pm} ->
  modPlus h (modPlus i j m) m = modPlus (modPlus h i m) j m
modPlusAssoc {h} {i} {j} {m} =
  let hCommIj: (modPlus h (modPlus i j m) m = modPlus (modPlus i j m) h m) =
        cong {f = \x => md x m} (plusCommutative h (modPlus i j m))
      hPlusIj: (modPlus (plus i j) h m = modPlus (modPlus i j m) h m) =
        modPlusMod {i = plus i j} {j = h}
      IjCommH: (modPlus (plus i j) h m = modPlus h (plus i j) m) =
        cong {f = \x => md x m} (plusCommutative (plus i j) h)
      assoc: (modPlus h (plus i j) m = modPlus (plus h i) j m) =
        cong {f = \x => md x m} (plusAssociative h i j)
      hiPlusJ: (modPlus (plus h i) j m = modPlus (modPlus h i m) j m) =
        modPlusMod {i = plus h i} {j = j}
  in  trans hCommIj (trans (sym hPlusIj) (trans IjCommH (trans assoc hiPlusJ)))

-- Combining a number with a proof that it is a valid modulus ------------------

||| Valid numbers modulo m (compare to Fin m)
data Mod: (m: Nat) -> Type where
  MkMod: {m: Nat} -> (i: Nat) -> ValidMod i m -> Mod m
  
-- Two Mods are equal when their values and moduli are equal -------------------

||| You can ignore validity proofs when saying two Mods are equal
eqMods: {m: Nat} -> (i = j) -> MkMod {m = m} i iValid = MkMod {m = m} j jValid
eqMods {iValid} {jValid} Refl with (ltUniq iValid jValid)
  eqMods {iValid = iValid} {jValid = iValid} Refl | Refl = Refl

-- Azad's definition of a group ------------------------------------------------

||| Algebraic group as an interface including the group axioms as propositions.
interface Group g where
  -- Structure.
  id : g
  inv : g -> g
  (+) : g -> g -> g
  -- Axioms.
  propAssoc : (a, b, c: g) -> a + (b + c) = (a + b) + c
  propLeftId : (x: g) -> id + x = x
  propRightId : (x: g) -> x + id = x
  propLeftInv : (x: g) -> inv x + x = id
  propRightInv : (x: g) -> x + inv x = id

-- Group implementation for Mod ------------------------------------------------

Group (Mod (S pm)) where
  id = MkMod Z (LTESucc LTEZero)
  inv {pm} (MkMod i iValid) = MkMod (modInv i (S pm)) modInvValid
  (+) {pm} (MkMod i iValid) (MkMod j jValid) =
    MkMod (modPlus i j (S pm)) modPlusValid
  propAssoc {pm} (MkMod a aValid) (MkMod b bValid) (MkMod c cValid) =
    let eq: (modPlus a (modPlus b c (S pm)) (S pm) =
             modPlus (modPlus a b (S pm)) c (S pm)) =
          modPlusAssoc
    in  eqMods eq
  propLeftId {pm} (MkMod x xValid) =
    let eq: (modPlus Z x (S pm) = x) = validMdSame xValid
    in  eqMods eq
  propRightId {pm} (MkMod x xValid) =
    let eq: (modPlus Z x (S pm) = x) = validMdSame xValid
        comm: (modPlus x Z (S pm) = modPlus Z x (S pm)) = modPlusComm
    in  eqMods (trans comm eq)
  propLeftInv {pm} (MkMod x xValid) =
    let eq: (modPlus x (modInv x (S pm)) (S pm) = Z) = modInvInverse
        comm: (modPlus (modInv x (S pm)) x (S pm) =
               modPlus x (modInv x (S pm)) (S pm)) =
          modPlusComm
    in  eqMods (trans comm eq)
  propRightInv {pm} (MkMod x xValid) =
    let eq: (modPlus x (modInv x (S pm)) (S pm) = Z) = modInvInverse
    in  eqMods eq

