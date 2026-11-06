(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From Stdlib Require PrimInt63 Uint63.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AxSymExec3K AxSymExec3BK AsanPlanCoreK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import FxCarryK FxImgK FxBaseK FxBlockK.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module EXIK.
Import PrimInt63.
Definition B61 : int := 2305843009213693952%uint63.
Definition i0 : int := 0%uint63.
End EXIK.

Module EXFK.
Import AX2K. Import AX2BK. Import CARFK.

Definition rel_litF (rb : expr) (rk : Z) (rn : Z) (kb : expr) (kk : Z) (kn : Z) : rangerel :=
  if BASFK.expr_eqbF rb kb then
    if (if Z.leb kk rk then Z.leb (rk + rn) (kk + kn) else false) then RInside (rk - kk)
    else if (if Z.leb (rk + rn) kk then true else Z.leb (kk + kn) rk) then RDisjoint
    else RPartial
  else RUnknown.

Local Open Scope Z_scope.

Fixpoint ctz_fuelF (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 0%Z
  | S f => if Z.odd z then 0%Z else (1 + ctz_fuelF f (Z.div2 z))%Z
  end.
Definition ctz64F (z : Z) : Z := ctz_fuelF 64 z.
Fixpoint ealign0F (kn : list kentry) (e : expr) {struct e} : Z :=
  match find_align kn e with
  | Some m => if Z.ltb 0 m then ctz64F m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64F (zmod64 z)
  | EAlu ALU_ADD a b => Z.min (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_SUB a b => Z.min (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_AND a b => Z.max (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_OR a b => Z.min (ealign0F kn a) (ealign0F kn b)
  | EAlu ALU_SLL a b =>
      match lit_shamt b with
      | Some s => Z.min (ealign0F kn a + s)%Z 64
      | None => 0%Z
      end
  | EMd M_MUL a b => Z.min (ealign0F kn a + ealign0F kn b)%Z 64
  | _ => 0%Z
  end
  end.

Definition ealignBF (bc : bctx) (e : expr) : Z := Z.max (ealign0F (bc_ffk bc) e) (pageup_align e).

Definition modp2 (x j : Z) : Z := if Z.leb 0 j then Z.land x (Z.ones j) else (x mod 2 ^ j)%Z.

Definition p2 (j : Z) : Z := if Z.leb 0 j then Z.shiftl 1 j else (2 ^ j)%Z.
Fixpoint lowbitsBF (bc : bctx) (e : expr) (j : Z) {struct e} : option Z :=
  let dflt := fun _ : unit => if Z.leb j (ealignBF bc e) then Some 0%Z else lin_lowbits_knB bc e j in
  match e with
  | ELit z => Some (modp2 (zmod64 z) j)
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb (modp2 (zmod64 c) j) 0 then Some 0%Z else
      match lowbitsBF bc a j with Some v => Some (Z.land v (modp2 (zmod64 c) j)) | None => dflt tt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbitsBF bc a j with Some v => Some (Z.lor v (modp2 (zmod64 c) j)) | None => dflt tt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbitsBF bc a j with Some v => Some (Z.lxor v (modp2 (zmod64 c) j)) | None => dflt tt end
  | EAlu ALU_ADD a b =>
      match lowbitsBF bc a j, lowbitsBF bc b j with Some x, Some y => Some (modp2 (x + y) j) | _, _ => dflt tt end
  | EAlu ALU_SUB a b =>
      match lowbitsBF bc a j, lowbitsBF bc b j with Some x, Some y => Some (modp2 (x - y) j) | _, _ => dflt tt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb (modp2 (zmod64 c) j) 0 then Some 0%Z else
      match lowbitsBF bc a j with Some v => Some (modp2 (c * v) j) | None => dflt tt end
  | _ => dflt tt
  end.

Definition lin_nowrapBF (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (BASFK.erangeBF bc) (fst l) (snd l) with
  | Some (lo, hi) => if Z.leb 0 lo then Z.ltb hi two64 else false
  | None => false
  end.
Definition lin_nowrap_lBF (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  match lin_range (BASFK.erangeBF bc) c ts with
  | Some (lo, hi) => if Z.leb 0 lo then Z.ltb hi two64 else false
  | None => false
  end.
Definition mkSrlBF (bc : bctx) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  if lin_trivial l then mkAlu ALU_SRL a (ELit s) else
  let m := (2 ^ s)%Z in
  let nw := lin_nowrapBF bc a in
  if (if coeffs_div m (snd l) then nw else false)
  then unlin ((fst l / m)%Z, ldiv_terms m (snd l))
  else
    match (if nw then lsplit_divc m (snd l) else ([], [])) with
    | ((_ :: _) as dts, (_ :: _) as rts) =>
        match (if lin_nowrap_lBF bc (fst l) rts then BASFK.erangeBF bc (unlin (fst l, rts)) else None) with
        | Some (lo, hi) =>
            if Z.eqb (lo / m) (hi / m) then unlin ((lo / m)%Z, ldiv_terms m dts)
            else mkAlu ALU_SRL a (ELit s)
        | None => mkAlu ALU_SRL a (ELit s)
        end
    | _ => mkAlu ALU_SRL a (ELit s)
    end.

Definition narrow_maskBF (bc : bctx) (a : expr) (k' : Z) : option Z :=
  let i := ctz64F k' in
  let pi := p2 i in
  let m := (k' + pi)%Z in
  let j := Z.log2 m in
  let pj := p2 j in
  if (if Z.ltb 0 k' then if Z.eqb m pj then Z.ltb j 64 else false else false) then
    match xhiB bc a with
    | Some h => if Z.ltb h pj then Some (two64 - pi)%Z else None
    | None => None
    end
  else None.

Definition mkAnd0BF (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      let k' := zmod64 k in
      let j := Z.log2 (two64 - k') in
      if (if Z.eqb (two64 - k') (p2 j) then Z.ltb j 64 else false) then

        (if Z.leb j (ealignBF bc a) then a
         else let l := lin_of a in
              if (negb (lin_trivial l) && coeffs_divkB bc (2 ^ j) (snd l))%bool
              then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
              else
                match (if lin_trivial l then ([], snd l) else lsplit_divB bc (2 ^ j) (snd l)) with
                | ((_ :: _) as dts, (_ :: _) as rts) => and_high_splitB bc b j (fst l) dts rts
                | _ =>
                       mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrlBF bc a j)
                end)
      else
        let j2 := Z.log2 (k' + 1) in
        if (if Z.eqb (k' + 1) (p2 j2) then Z.ltb j2 64 else false) then

          (if Z.leb j2 (ealignBF bc a) then ELit 0
           else match lowbitsBF bc a j2 with
           | Some v => ELit v
           | None =>
           if lin_trivial (lin_of a) then mkAlu ALU_AND a b
           else match lin_lowbits_knB bc a j2 with
                | Some v => ELit v
                | None =>
                    match lsplit_divB bc (2 ^ j2) (snd (lin_of a)) with
                    | (_ :: _, (_ :: _) as rts) => and_low_splitB bc b j2 (fst (lin_of a)) rts
                    | _ => mkAlu ALU_AND a b
                    end
                end
           end)
        else
          let j3 := (Z.log2 k' + 1)%Z in
          if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool then
            match lin_lowbits_knB bc a j3 with
            | Some v => ELit (Z.land v k')
            | None => mkAlu ALU_AND a b
            end
          else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.

Definition mkAndBF (bc : bctx) (a b : expr) : expr :=
  match b with
  | ELit k =>
      match narrow_maskBF bc a (zmod64 k) with
      | Some m => mkAnd0BF bc a (ELit m)
      | None => mkAnd0BF bc a b
      end
  | _ => mkAnd0BF bc a b
  end.

Definition mkAndKBF (bc : bctx) (a b : expr) : expr :=
  match a, b with
  | EAlu ALU_AND x (ELit m1), ELit k => mkAndBF bc x (ELit (Z.land (zmod64 m1) (zmod64 k))%Z)
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>

      let i' := ((i mod two64) mod 64)%Z in
      if Z.eqb (m mod two64) (2 ^ i') then mkAndBF bc x (ELit (Z.land (two64 - 2 ^ i') (k mod two64))%Z)
      else mkAndBF bc a b
  | _, _ => mkAndBF bc a b
  end.

Definition or_disjointBF (bc : bctx) (a b : expr) : bool :=
  match BASFK.erangeBF bc b with
  | Some (lo, hi) => if Z.leb 0 lo then Z.ltb hi (2 ^ (ealignBF bc a)) else false
  | None => false
  end.
Definition mkOrBF (bc : bctx) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu ALU_OR x y)
  | _, _ =>
      if or_disjointBF bc a b then mkAlu ALU_ADD a b
      else if or_disjointBF bc b a then mkAlu ALU_ADD a b
      else match b with
           | ELit c => mkAlu ALU_ADD (mkAndKBF bc a (ELit (Z.lnot (c mod two64)))) (ELit c)
           | _ => match a with
                  | ELit c => mkAlu ALU_ADD (mkAndKBF bc b (ELit (Z.lnot (c mod two64)))) (ELit c)
                  | _ => EAlu ALU_OR a b
                  end
           end
  end.

Definition mkAluK0BF (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_SLTU => mkSltB bc BC_LTU ALU_SLTU a b
  | ALU_SLT => mkSltB bc BC_LT ALU_SLT a b
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAndBF bc a b
               | ELit _, _ => mkAndKBF bc b a
               | _, _ => mkAndKBF bc a b
               end
  | ALU_OR => if BASFK.expr_eqbF a b then a else mkOrBF bc a b
  | ALU_XOR => if BASFK.expr_eqbF a b then ELit 0 else match is_lit a, b with
               | None, ELit k => if Z.eqb (zmod64 k) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
                                else mkAlu op a b
               | _, _ => BASFK.mkAluL op a b
               end
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrlBF bc a s
               | _, _ => mkAlu op a b
               end
  | _ => BASFK.mkAluL op a b
  end.

Definition mkAluKBF (bc : bctx) (op : aluop) (a b : expr) : expr :=
  BASFK.foldKBG bc (mkAluK0BF bc op a b).

Definition mkMdKBF (bc : bctx) (op : mulop) (a b : expr) : expr :=
  match is_lit a, op, b with
  | None, M_REMU, ELit m =>
      match pow2_log m with
      | Some k => mkAluKBF bc ALU_AND a (ELit (2 ^ k - 1))
      | None => mkMd op a b
      end
  | None, M_DIVU, ELit m =>
      match pow2_log m with
      | Some k => mkAluKBF bc ALU_SRL a (ELit k)
      | None => mkMd op a b
      end
  | _, _, _ => mkMd op a b
  end.

Definition amo_newvalBF (bc : bctx) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
  match aop with
  | None => src
  | Some o => match wd with AW => mkAluwKB bc o old src | AD => mkAluKBF bc o old src end
  end.

Local Close Scope Z_scope.

Definition ranges_apartBF (bc : bctx) (kd : list kentry) (br1 : option (Z * Z)) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if BASFK.expr_eqbF b2 b1 then (if Z.leb (k1 + n1) k2 then true else Z.leb (k2 + n2) k1)%Z else
  if (match br1, base_rangeB bc b2 with
      | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + k1 + n1) (lo2 + k2) then true else Z.leb (hi2 + k2 + n2) (lo1 + k1)
      | _, _ => false
      end)%Z then true
  else if kdisj_apartB bc kd b1 k1 n1 b2 k2 n2 then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Fixpoint log_lookupBF (bc : bctx) (kd : list kentry) (obr : option (option (Z * Z))) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_litF rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupBF bc kd obr rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let br1 := match obr with Some r => r | None => base_rangeB bc rb end in
          if ranges_apartBF bc kd br1 rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupBF bc kd (Some br1) rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupBF bc kd (Some br1) rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.

Definition ranges_apartBF2 (bc : bctx) (kd : list kentry) (sp : sprep) (br1 : option (Z * Z)) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if BASFK.expr_eqbF b2 b1 then (if Z.leb (k1 + n1) k2 then true else Z.leb (k2 + n2) k1)%Z else
  if (match br1, sp_rng sp with
      | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + k1 + n1) (lo2 + k2) then true else Z.leb (hi2 + k2 + n2) (lo1 + k1)
      | _, _ => false
      end)%Z then true
  else if (if Z.eqb (zlit64 n2) n2 then in_sidesB bc (sp_D sp) b1 k1 n1 else kdisj_apartB bc kd b1 k1 n1 b2 k2 n2) then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Fixpoint log_lookupBF2 (bc : bctx) (kd : list kentry) (obr : option (option (Z * Z))) (log : list sentry) (lis : list sprep) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log, lis with
  | [], _ => LMiss acc hints
  | SE (SA kb kk) w v :: rest, li :: lrest =>
      match rel_litF rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupBF2 bc kd obr rest lrest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let br1 := match obr with Some r => r | None => base_rangeB bc rb end in
          if ranges_apartBF2 bc kd li br1 rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupBF2 bc kd (Some br1) rest lrest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupBF2 bc kd (Some br1) rest lrest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  | _ :: _, [] => log_lookupBF bc kd obr log rb rk n sx hints acc
  end.

Definition zb (z : Z) : option PrimInt63.int := BASFK.zb z.

Record sann : Type := SAN { sa_zw : Z; sa_rng : option (PrimInt63.int * PrimInt63.int) }.
Definition sann_sp (sp : sprep) (e : sentry) : sann :=
  let zw := Z.of_nat (e_width e) in
  SAN zw (match sp_rng sp with
          | Some (lo2, hi2) =>
              match zb (lo2 + a_off (e_addr e))%Z, zb (hi2 + a_off (e_addr e) + zw)%Z with
              | Some x, Some y => Some (x, y)
              | _, _ => None
              end
          | None => None
          end).
Definition rann (br1 : option (Z * Z)) (rk n : Z) : option (PrimInt63.int * PrimInt63.int) :=
  match br1 with
  | Some (lo1, hi1) =>
      match zb (lo1 + rk)%Z, zb (hi1 + rk + n)%Z with
      | Some x, Some y => Some (x, y)
      | _, _ => None
      end
  | None => None
  end.

Definition rann63 (e63 : option (PrimInt63.int * PrimInt63.int)) (br1 : option (Z * Z)) (rk n : Z) : option (PrimInt63.int * PrimInt63.int) :=
  match e63 with
  | Some (lo63, hi63) =>
      match zb rk, IMGFK.z61 n with
      | Some k63, Some n63 =>
          Some (PrimInt63.sub (PrimInt63.add lo63 k63) EXIK.B61, PrimInt63.add (PrimInt63.sub (PrimInt63.add hi63 k63) EXIK.B61) n63)
      | _, _ => rann br1 rk n
      end
  | None => rann br1 rk n
  end.
Definition i63apart (ra sa : option (PrimInt63.int * PrimInt63.int)) : bool :=
  match ra, sa with
  | Some (rlo, rhi), Some (slo, shi) => if PrimInt63.leb rhi slo then true else PrimInt63.leb shi rlo
  | _, _ => false
  end.
Fixpoint log_lookupBF3 (bc : bctx) (kd : list kentry) (br1 : option (Z * Z)) (ra : option (PrimInt63.int * PrimInt63.int))
         (log : list sentry) (lis : list sprep) (lia : list sann)
         (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match log, lis, lia with
  | [], _, _ => LMiss acc hints
  | SE (SA kb kk) w v :: rest, li :: lrest, sa :: arest =>
      match rel_litF rb rk zn kb kk (sa_zw sa) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupBF3 bc kd br1 ra rest lrest arest rb rk n zn sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if (if i63apart ra (sa_rng sa) then true else ranges_apartBF2 bc kd li br1 rb rk zn kb kk (sa_zw sa))
          then log_lookupBF3 bc kd br1 ra rest lrest arest rb rk n zn sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupBF3 bc kd br1 ra rest lrest arest rb rk n zn sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  | _, _, _ => log_lookupBF2 bc kd (Some br1) log lis rb rk n sx hints acc
  end.

Definition ivof (k w : Z) : option (PrimInt63.int * PrimInt63.int) :=
  match zb k, IMGFK.z61 w with
  | Some s, Some w63 => Some (s, PrimInt63.add s w63)
  | _, _ => None
  end.
Record lent : Type := LE { le_k : Z; le_zw : Z; le_w : nat; le_v : expr; le_iv : option (PrimInt63.int * PrimInt63.int) }.

Definition ibucket (idx : ptree (list lent)) (k : Z) : list lent := match pt_get idx (kx_gkey k) with Some l => l | None => [] end.
Definition idx_add (idx : ptree (list lent)) (en : lent) : ptree (list lent) :=
  pt_set (kx_gkey (le_k en)) (en :: ibucket idx (le_k en)) idx.
Record lgroup : Type := LG { lg_b : expr; lg_hull : option (PrimInt63.int * PrimInt63.int); lg_es : list lent;
                             lg_cnt : Z; lg_wmax : Z; lg_idx : ptree (list lent) }.
Definition hull_join (h r : option (PrimInt63.int * PrimInt63.int)) : option (PrimInt63.int * PrimInt63.int) :=
  match h, r with
  | Some (a, b), Some (c, d) => Some (if PrimInt63.ltb c a then c else a, if PrimInt63.ltb b d then d else b)
  | _, _ => None
  end.
Fixpoint gl_add (gl : list lgroup) (kb : expr) (en : lent) (rng : option (PrimInt63.int * PrimInt63.int)) : list lgroup :=
  match gl with
  | [] => [LG kb rng [en] 1 (le_zw en) (idx_add PTLeaf en)]
  | g :: r => if BASFK.expr_eqbF kb (lg_b g)
              then LG (lg_b g) (hull_join (lg_hull g) rng) (en :: lg_es g) (lg_cnt g + 1)%Z (Z.max (lg_wmax g) (le_zw en)) (idx_add (lg_idx g) en) :: r
              else g :: gl_add r kb en rng
  end.
Definition gl_adde (gl : list lgroup) (e : sentry) (sa : sann) : list lgroup :=
  gl_add gl (a_base (e_addr e)) (LE (a_off (e_addr e)) (sa_zw sa) (e_width e) (e_val e) (ivof (a_off (e_addr e)) (sa_zw sa))) (sa_rng sa).
Fixpoint GLof (f : sentry -> sprep) (log : list sentry) : list lgroup :=
  match log with
  | [] => []
  | e :: rest => gl_adde (GLof f rest) e (sann_sp (f e) e)
  end.
Fixpoint gl_others_apart (gl : list lgroup) (rb : expr) (ra : option (PrimInt63.int * PrimInt63.int)) : bool :=
  match gl with
  | [] => true
  | g :: r => if BASFK.expr_eqbF rb (lg_b g) then gl_others_apart r rb ra
              else if i63apart ra (lg_hull g) then gl_others_apart r rb ra else false
  end.
Fixpoint gl_find (gl : list lgroup) (rb : expr) : list lent :=
  match gl with
  | [] => []
  | g :: r => if BASFK.expr_eqbF rb (lg_b g) then lg_es g else gl_find r rb
  end.
Fixpoint le_scan (es : list lent) (rk zn : Z) (n : nat) (sx : bool) (hints : list bool) : option lres :=
  match es with
  | [] => Some (LMiss [] hints)
  | LE kk zw w v _ :: r =>
      if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zw) else false)%Z then Some (LHit (mkExt sx (Z.to_nat (rk - kk)) n v) [] hints)
      else if (if Z.leb (rk + zn) kk then true else Z.leb (kk + zw) rk)%Z then le_scan r rk zn n sx hints
      else None
  end.
Fixpoint le_scanI (es : list lent) (qi : option (PrimInt63.int * PrimInt63.int)) (rk zn : Z) (n : nat) (sx : bool) (hints : list bool) : option lres :=
  match es with
  | [] => Some (LMiss [] hints)
  | LE kk zw w v iv :: r =>
      match iv, qi with
      | Some (s, e), Some (q, qe) =>
          if (if PrimInt63.leb s q then PrimInt63.leb qe e else false) then Some (LHit (mkExt sx (Z.to_nat (rk - kk)) n v) [] hints)
          else if (if PrimInt63.leb qe s then true else PrimInt63.leb e q) then le_scanI r qi rk zn n sx hints
          else None
      | _, _ =>
          if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zw) else false)%Z then Some (LHit (mkExt sx (Z.to_nat (rk - kk)) n v) [] hints)
          else if (if Z.leb (rk + zn) kk then true else Z.leb (kk + zw) rk)%Z then le_scanI r qi rk zn n sx hints
          else None
      end
  end.
Fixpoint gl_findg (gl : list lgroup) (rb : expr) : option lgroup :=
  match gl with
  | [] => None
  | g :: r => if BASFK.expr_eqbF rb (lg_b g) then Some g else gl_findg r rb
  end.
Definition le_disj (e : lent) (rk zn : Z) : bool := (if Z.leb (rk + zn) (le_k e) then true else Z.leb (le_k e + le_zw e) rk)%Z.
Fixpoint bucket_clear (l : list lent) (rk zn : Z) : bool :=
  match l with [] => true | e :: r => if le_disj e rk zn then bucket_clear r rk zn else false end.
Fixpoint win_clear (idx : ptree (list lent)) (k : Z) (cnt : nat) (rk zn : Z) : bool :=
  match cnt with
  | O => true
  | S c => if bucket_clear (ibucket idx k) rk zn then win_clear idx (k + 1)%Z c rk zn else false
  end.
Definition grp_miss (g : lgroup) (rk zn : Z) : bool :=
  (if Z.ltb 24 (lg_cnt g) then if Z.ltb 0 zn then if Z.ltb 0 (lg_wmax g) then if Z.ltb (lg_wmax g) 65 then
     win_clear (lg_idx g) (rk - lg_wmax g + 1) (Z.to_nat (lg_wmax g + zn - 1)) rk zn
   else false else false else false else false)%Z.
Definition grp_scan (gl : list lgroup) (rb : expr) (rk zn : Z) (n : nat) (sx : bool) (hints : list bool) : option lres :=
  match gl_findg gl rb with
  | Some g => if grp_miss g rk zn then Some (LMiss [] hints) else le_scanI (lg_es g) (ivof rk zn) rk zn n sx hints
  | None => Some (LMiss [] hints)
  end.
Definition log_lookupG (bc : bctx) (kd : list kentry) (br1 : option (Z * Z)) (ra : option (PrimInt63.int * PrimInt63.int))
           (gl : list lgroup) (log : list sentry) (lis : list sprep) (lia : list sann)
           (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (hints : list bool) : lres :=
  match (if gl_others_apart gl rb ra then grp_scan gl rb rk zn n sx hints else None) with
  | Some r => r
  | None => log_lookupBF3 bc kd br1 ra log lis lia rb rk n zn sx hints []
  end.

Fixpoint wr_numB (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if BASFK.expr_eqbF (a_base a) kb then Z.leb kk (a_off a) else false) then
        match xloB bc len with
        | Some l => if Z.leb (a_off a + Z.of_nat n) (kk + l) then true else wr_numB bc rest a n
        | None => wr_numB bc rest a n
        end
      else wr_numB bc rest a n
  | _ :: rest => wr_numB bc rest a n
  end.
Definition storeok_scBF (bc : bctx) (ex : bext) (a : saddr) (n : nat) : list sidecond :=
  if (if wr_numB bc (be_kw ex) a n then true else wr_coveredB bc (be_kw ex) a n) then [] else [SCStoreOk a n].

Fixpoint know_lookupA0F (bc : bctx) (st : option (list IMGFK.sgi)) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (zn : Z) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0F bc st in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          if BASFK.expr_eqbF rb kb then
            (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + Z.of_nat w) else false) then LHit (mkExt sx (Z.to_nat (rk - kk)) n v) acc hints
             else know_lookup segs rest rb rk n zn sx hints acc)
          else know_lookup segs rest rb rk n zn sx hints acc
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              if BASFK.expr_eqbF rb kb then
                (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zmod64 l0) else false) then LHit (ELit 0) acc hints
                 else know_lookup segs rest rb rk n zn sx hints acc)
              else

                  if xinsideB bc rb rk (ELit zn) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n zn sx hs acc
                  | [] => know_lookup segs rest rb rk n zn sx [] acc
                  end
          | _ =>
              if xinsideB bc rb rk (ELit zn) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n zn sx hs acc
              | [] => know_lookup segs rest rb rk n zn sx [] acc
              end
          end
      | KFill (SA kb kk) len c =>

          match len with
          | ELit l0 =>
              if BASFK.expr_eqbF rb kb then
                (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zmod64 l0) else false) then LHit (fill_lit sx n c) acc hints
                 else know_lookup segs rest rb rk n zn sx hints acc)
              else
                  if xinsideB bc rb rk (ELit zn) kb kk len then LHit (fill_lit sx n c) acc hints else
                  match hints with
                  | true :: hs => LHit (fill_lit sx n c) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n zn sx hs acc
                  | [] => know_lookup segs rest rb rk n zn sx [] acc
                  end
          | _ =>
              if xinsideB bc rb rk (ELit zn) kb kk len then LHit (fill_lit sx n c) acc hints else
              match hints with
              | true :: hs => LHit (fill_lit sx n c) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n zn sx hs acc
              | [] => know_lookup segs rest rb rk n zn sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n zn sx hints acc
      | KBlob (SA kb kk) len k =>
          if BASFK.expr_eqbF rb kb then

            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + zn) (kk + (zmod64 l0))
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (zmod64 l0)) rk then know_lookup segs rest rb rk n zn sx hints acc
                  else LStuck
              | _ =>

                  if match erangeB bc len with
                     | Some (lo, _) => Z.leb (rk + zn) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n zn sx hs acc
                  | [] => know_lookup segs rest rb rk n zn sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n zn sx hints acc
          else know_lookup segs rest rb rk n zn sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (if Z.leb lo rk then Z.leb (rk + zn) hi else false) then
                match IMGFK.img_bytesFF st segs rk n with
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n zn sx hints acc
          | _ => know_lookup segs rest rb rk n zn sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n zn sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n zn sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n zn sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n zn sx hints acc
      end
  end.

Definition annw (K : kentry) : option (PrimInt63.int * PrimInt63.int) :=
  match K with
  | KWord (SA _ kk) w _ =>
      match zb kk, IMGFK.z61 (Z.of_nat w) with
      | Some s, Some w63 => Some (s, PrimInt63.add s w63)
      | _, _ => None
      end
  | _ => None
  end.
Definition qann (rk zn : Z) : option (PrimInt63.int * PrimInt63.int) :=
  match zb rk, IMGFK.z61 zn with Some a, Some b => Some (a, b) | _, _ => None end.

Definition keepL (K : kentry) : bool :=
  match K with
  | KZero (SA kb _) _ | KFill (SA kb _) _ _ => novars kb
  | _ => true
  end.
Record xctx : Type := XC { xc_st : option (list IMGFK.sgi); xc_fw : list (option (PrimInt63.int * PrimInt63.int) * kentry);
                           xc_w0 : list (positive * kentry) }.
Definition mk_xc (segs : list Segment) (kx : kix) : xctx :=
  XC (IMGFK.mk_stab segs) (List.map (fun K => (annw K, K)) (kx_wf kx)) (List.filter (fun t => keepL (snd t)) (kx_w0 kx)).

Definition xinside_numBr (bc : bctx) (br1 : option (Z * Z)) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xloB bc b2, xhiB bc b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match br1, xhiB bc n1, xloB bc n2 with
        | Some (lo1, hi1), Some h1, Some l2 => (Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2))%bool%Z
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Definition xinsideBr (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
  else if novars b2 then
         (if xinside_numBr bc br1 k1 n1 b2 k2 n2 then true
          else match n1 with ELit _ => false | _ => xinside0B bc b1 k1 n1 b2 k2 n2 end)
       else false.

Local Open Scope Z_scope.
Definition kstepF (bc : bctx) (st : option (list IMGFK.sgi)) (segs : list Segment) (br : option (Z * Z)) (K : kentry) (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool)
           (acc : list sidecond) (k : unit -> lres) : lres :=
  match K with
  | KWord (SA kb kk) w v =>
      if BASFK.expr_eqbF rb kb then
        (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + Z.of_nat w) else false) then LHit (mkExt sx (Z.to_nat (rk - kk)) n v) acc []
         else k tt)
      else k tt
  | KZero (SA kb kk) len =>
      match len with
      | ELit l0 =>
          if BASFK.expr_eqbF rb kb then
            (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zmod64 l0) else false) then LHit (ELit 0) acc [] else k tt)
          else if xinsideBr bc br rb rk (ELit zn) kb kk len then LHit (ELit 0) acc [] else k tt
      | _ => if xinsideBr bc br rb rk (ELit zn) kb kk len then LHit (ELit 0) acc [] else k tt
      end
  | KFill (SA kb kk) len c =>
      match len with
      | ELit l0 =>
          if BASFK.expr_eqbF rb kb then
            (if (if Z.leb kk rk then Z.leb (rk + zn) (kk + zmod64 l0) else false) then LHit (fill_lit sx n c) acc [] else k tt)
          else if xinsideBr bc br rb rk (ELit zn) kb kk len then LHit (fill_lit sx n c) acc [] else k tt
      | _ => if xinsideBr bc br rb rk (ELit zn) kb kk len then LHit (fill_lit sx n c) acc [] else k tt
      end
  | KBlob (SA kb kk) len bk =>
      if BASFK.expr_eqbF rb kb then
        if Z.leb kk rk then
          match len with
          | ELit l0 =>
              if Z.leb (rk + zn) (kk + (zmod64 l0)) then LHit (EBlob sx bk (rk - kk) n) acc []
              else if Z.leb (kk + (zmod64 l0)) rk then k tt
              else LStuck
          | _ =>
              if match erangeB bc len with
                 | Some (lo, _) => Z.leb (rk + zn) (kk + lo)
                 | None => false
                 end
              then LHit (EBlob sx bk (rk - kk) n) acc []
              else k tt
          end
        else k tt
      else k tt
  | KImg lo hi =>
      match rb with
      | ELit 0 =>
          if (if Z.leb lo rk then Z.leb (rk + zn) hi else false) then
            match IMGFK.img_bytesFF st segs rk n with
            | Some bs => LHit (lit_of_bytes sx n bs) acc []
            | None => LStuck
            end
          else k tt
      | _ => k tt
      end
  | _ => k tt
  end.
Local Close Scope Z_scope.
Fixpoint kwalkfF (bc : bctx) (st : option (list IMGFK.sgi)) (segs : list Segment) (br : option (Z * Z)) (l : list (option (PrimInt63.int * PrimInt63.int) * kentry))
         (r : option (PrimInt63.int * PrimInt63.int)) (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (acc : list sidecond) : lres :=
  match l with
  | [] => LMiss acc []
  | (a, K) :: rest =>
      if (match a, r with
          | Some (s, e), Some (r63, zn63) => if PrimInt63.leb s r63 then PrimInt63.leb (PrimInt63.add r63 zn63) e else false
          | _, _ => true
          end)
      then kstepF bc st segs br K rb rk n zn sx acc (fun _ => kwalkfF bc st segs br rest r rb rk n zn sx acc)
      else kwalkfF bc st segs br rest r rb rk n zn sx acc
  end.

Local Open Scope Z_scope.
Definition know_lookupA0IF (bc : bctx) (kx : kix) (xc : xctx) (br : option (Z * Z)) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match hints, n with
  | [], S _ =>
      if is_lit0 rb then know_lookupA0F bc (xc_st xc) segs (kx_merge (kx_bucket (kx_gran kx) (gran rk)) (xc_w0 xc)) rb rk n (Z.of_nat n) sx [] acc
      else let zn := Z.of_nat n in kwalkfF bc (xc_st xc) segs br (xc_fw xc) (qann rk zn) rb rk n zn sx acc
  | _, _ => know_lookupA0F bc (xc_st xc) segs (kx_kn kx) rb rk n (Z.of_nat n) sx hints acc
  end.

Definition know_lookupABIF (bc : bctx) (kx : kix) (xc : xctx) (br : option (Z * Z)) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0IF bc kx xc br segs rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.

Local Close Scope Z_scope.

Definition bv_signedG {n : N} (b : bv n) : Z :=
  let u := bv_unsigned b in let h := Z.shiftl 1 (Z.of_N n - 1) in if Z.ltb u h then u else u - Z.shiftl h 1.

Definition bv_signedF {n : N} (b : bv n) : Z :=
  if N.eqb n 12 then let u := bv_unsigned b in if Z.ltb u 2048 then u else u - 4096
  else if N.eqb n 13 then let u := bv_unsigned b in if Z.ltb u 4096 then u else u - 8192
  else if N.eqb n 21 then let u := bv_unsigned b in if Z.ltb u 1048576 then u else u - 2097152
  else if N.eqb n 20 then let u := bv_unsigned b in if Z.ltb u 524288 then u else u - 1048576
  else bv_signedG b.

Definition flat_scBF (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  match base_rangeB bc (a_base a) with
  | Some (lo, hi) =>
      if (if Z.leb 0 (lo + a_off a) then Z.leb (hi + a_off a + Z.of_nat n) two64 else false)%Z
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.

Definition zsx32F (v : Z) : Z := zmod64 (modp2 (v + 2147483648) 32 - 2147483648)%Z.

Definition zband32BF (bc : bctx) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (BASFK.erangeBF bc) (fst l) (snd l) with
  | Some (lo, hi) => if Z.ltb (- 2 ^ 31) lo then Z.ltb hi (2 ^ 31) else false
  | None => false
  end.
Definition mkAluwK0BF (bc : bctx) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD | ALU_SUB =>
      let d := mkAlu op a b in
      match is_lit d with
      | Some v => ELit (zsx32F v)
      | None => match BASFK.erangeBF bc d with
                | Some (lo, hi) => if sx32_stable lo hi then d else if zband32BF bc d then d else mkAluw op a b
                | None => if zband32BF bc d then d else mkAluw op a b
                end
      end
  | _ => mkAluw op a b
  end.
Definition mkAluwKBF (bc : bctx) (op : aluop) (a b : expr) : expr := BASFK.foldKBG bc (mkAluwK0BF bc op a b).

Definition conc_exprBF (bc : bctx) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match BASFK.concretizeBG bc e with Some v => ELit v | None => e end
  end.
Definition enum_branchBF (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match BASFK.concretizeBG bc e with
  | Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
  | None => None
  end.

Definition p2n5 (p : positive) : nat :=
  match p with
  | 1%positive => 1 | 2%positive => 2 | 3%positive => 3 | 4%positive => 4 | 5%positive => 5 | 6%positive => 6 | 7%positive => 7
  | 8%positive => 8 | 9%positive => 9 | 10%positive => 10 | 11%positive => 11 | 12%positive => 12 | 13%positive => 13
  | 14%positive => 14 | 15%positive => 15 | 16%positive => 16 | 17%positive => 17 | 18%positive => 18 | 19%positive => 19
  | 20%positive => 20 | 21%positive => 21 | 22%positive => 22 | 23%positive => 23 | 24%positive => 24 | 25%positive => 25
  | 26%positive => 26 | 27%positive => 27 | 28%positive => 28 | 29%positive => 29 | 30%positive => 30 | 31%positive => 31
  | _ => Pos.to_nat p
  end%nat.
Definition ridxF (r : reg) : nat := match bv_unsigned r with Zpos p => p2n5 p | _ => O end.
Definition sr_getF (sr : list expr) (r : reg) : expr := if bv_eqb r 0 then ELit 0 else nth (ridxF r) sr (ELit 0).
Definition ssetF (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SSR npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) e) (s_log ss) (s_know ss) (s_next ss) (s_resv ss).

Definition lit_branchF (c : branch_cond) (x y : Z) : bool :=
  let x' := zmod64 x in let y' := zmod64 y in
  match c with
  | BC_EQ => Z.eqb x' y'
  | BC_NE => negb (Z.eqb x' y')
  | BC_LT => Z.ltb (zsigned64 x') (zsigned64 y')
  | BC_GE => negb (Z.ltb (zsigned64 x') (zsigned64 y'))
  | BC_LTU => Z.ltb x' y'
  | BC_GEU => negb (Z.ltb x' y')
  end.
Definition decide_branchBF (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branchF c x y)
  | _, _ =>

      if BASFK.expr_eqbF a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match (match BASFK.erangeBF bc a, BASFK.erangeBF bc b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end) with
             | Some t => Some t
             | None => lin_branchB bc c a b
             end
           end
  end.

Definition decide_branchBF_h (bc : bctx) (cache : BASFK.bcache) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branchF c x y)
  | _, _ =>
      if BASFK.expr_eqbF a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match (match BASFK.erange_h bc cache a, BASFK.erange_h bc cache b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end) with
             | Some t => Some t
             | None => lin_branchB bc c a b
             end
           end
  end.

Definition sym_readBIF (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupBF2 bc (be_kd ex) None (s_log ss) lis (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scBF bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABIF bc kx xc (base_rangeB bc (a_base a)) segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scBF bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>

          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scBF bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.

Definition flat_scBFr (br : option (Z * Z)) (a : saddr) (n : nat) : list sidecond :=
  match br with
  | Some (lo, hi) =>
      if (if Z.leb 0 (lo + a_off a) then Z.leb (hi + a_off a + Z.of_nat n) two64 else false)%Z
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.

Definition flat_scBFa (ra : option (PrimInt63.int * PrimInt63.int)) (br : option (Z * Z)) (a : saddr) (n : nat) : list sidecond :=
  match ra with
  | Some (x, _) => if PrimInt63.leb EXIK.B61 x then [] else [SCFlat a (elen n)]
  | None => flat_scBFr br a n
  end.
Definition sym_readBIFr (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep)
           (lia : list sann) (gl : list lgroup) (c : BASFK.bcache) (scr : scripts)
           (br : option (Z * Z)) (e63 : option (PrimInt63.int * PrimInt63.int)) (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) * BASFK.bcache :=
  let zn := Z.of_nat n in
  let ra := rann63 e63 br (a_off a) zn in
  match log_lookupG bc (be_kd ex) br ra gl
          (s_log ss) lis lia (a_base a) (a_off a) n zn sx' (sc_hints scr) with
  | LStuck => (None, c)
  | LHit v scs hints =>
      let '(v', c') := BASFK.foldKB_c bc c (extK0B bc v) in
      (Some (v', flat_scBFa ra br a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss), c')
  | LMiss scs hints =>
      match know_lookupABIF bc kx xc br segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => (None, c)
      | LHit v scs' hints' =>
          let '(v', c') := BASFK.foldKB_c bc c (extK0B bc v) in
          (Some (v', flat_scBFa ra br a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss), c')
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          (Some (rv, flat_scBFa ra br a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i), c)
      end
  end.

Definition sym_stepBIF (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_getF (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (ssetF ss rd (mkAluKBF bc op (g rs) (ELit (bv_signedF imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (ssetF ss rd (mkAluKBF bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (ssetF ss rd (mkAluKBF bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (ssetF ss rd (mkAluwKBF bc ALU_ADD (g rs) (ELit (bv_signedF imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (ssetF ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (ssetF ss rd (mkAluwKBF bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (ssetF ss rd (mkMdKBF bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (ssetF ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (ssetF ss rd (ELit (zmod64 (Z.shiftl (bv_signedF imm) 12))) (p + 4)) [] scr
  | Auipc rd imm => SOk (ssetF ss rd (ELit (zmod64 (Z.shiftl (bv_signedF imm) 12 + p))) (p + 4)) [] scr
  | Jal rd imm => SOk (ssetF ss rd (ELit (p + 4)) (zmod64 (p + bv_signedF imm))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprBF bc (g rs1) with
      | ELit z => SOk (ssetF ss rd (ELit (p + 4)) (zmod64 (Z.land (zmod64 z + bv_signedF imm) (-2)))) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let a := g rs1 in let b := g rs2 in
      match match decide_branchBF bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprBF bc a) (conc_exprBF bc b) with
                      | Some t => Some t
                      | None => enum_branchBF bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then zmod64 (p + bv_signedF imm) else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then zmod64 (p + bv_signedF imm) else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in

      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signedF imm) in
      match sym_readBIF segs ss bc kx xc ex lis scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signedF imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scBF bc a n ++ storeok_scBF bc ex a n) scr
      end

  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBIF segs ss bc kx xc ex lis scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scBF bc a n ++ storeok_scBF bc ex a n) scr
            else SStop
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readBIF segs ss bc kx xc ex lis scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) vold)
                             (SE a n (amo_newvalBF bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scBF bc ex a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.

Definition sym_stepBIF_c (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (c : BASFK.bcache) (segs : list Segment)
           (i : instr) (ss : sym_state) (scr : scripts) : stepres * BASFK.bcache :=
  let g r := sr_getF (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm =>
      match op with
      | ALU_ADD => let '(v, c1) := BASFK.mkAluKB_add_c bc c (g rs) (bv_signedF imm) in (SOk (ssetF ss rd v (p + 4)) [] scr, c1)
      | _ =>
             let '(v, c1) := BASFK.foldKB_c bc c (mkAluK0BF bc op (g rs) (ELit (bv_signedF imm))) in (SOk (ssetF ss rd v (p + 4)) [] scr, c1)
      end
  | ShiftImm op rd rs sh =>
      let '(v, c1) := BASFK.foldKB_c bc c (mkAluK0BF bc op (g rs) (ELit (bv_unsigned sh))) in (SOk (ssetF ss rd v (p + 4)) [] scr, c1)
  | Op op rd rs1 rs2 =>
      match op, g rs2 with
      | ALU_ADD, ELit z => let '(v, c1) := BASFK.mkAluKB_add_c bc c (g rs1) z in (SOk (ssetF ss rd v (p + 4)) [] scr, c1)
      | _, _ => let '(v, c1) := BASFK.foldKB_c bc c (mkAluK0BF bc op (g rs1) (g rs2)) in (SOk (ssetF ss rd v (p + 4)) [] scr, c1)
      end
  | Branch cnd rs1 rs2 imm =>
      let a := g rs1 in let b := g rs2 in
      (match match decide_branchBF_h bc c cnd a b with
             | Some t => Some t
             | None => match decide_branchB bc cnd (conc_exprBF bc a) (conc_exprBF bc b) with
                       | Some t => Some t
                       | None => enum_branchBF bc cnd a b
                       end
             end with
       | Some t => SOk (sjump ss (if t then zmod64 (p + bv_signedF imm) else p + 4)) [] scr
       | None =>
           match sc_dirs scr with
           | [] => SStop
           | t :: dirs' =>
               SOk (sjump ss (if t then zmod64 (p + bv_signedF imm) else p + 4)) [SCBr t cnd a b]
                   (SCR dirs' (sc_reads scr) (sc_hints scr))
           end
       end, c)
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      let sx' := match sz with SZ8 => false | _ => sx end in
      let '(a, c1) := BASFK.to_saddrKB_c bc c (g rs) (bv_signedF imm) in
      let '(br, e63, c2) := BASFK.base_range63_c bc c1 (a_base a) in
      let '(r, c3) := sym_readBIFr segs ss bc kx xc ex lis lia gl c2 scr br e63 a n sx' in
      (match r with
       | None => SStop
       | Some (v, scs, scr', nx') =>
           SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                    (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
       end, c3)
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let '(a, c1) := BASFK.to_saddrKB_c bc c (g rs1) (bv_signedF imm) in
      match resv_inval (s_resv ss) a with
      | None => (SStop, c1)
      | Some r' =>
          let '(br, c2) := BASFK.base_range_c bc c1 (a_base a) in
          (SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
               (flat_scBFr br a n ++ storeok_scBF bc ex a n) scr, c2)
      end

  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let '(a, c1) := BASFK.to_saddrKB_c bc c e 0 in
        let '(br, e63, c2) := BASFK.base_range63_c bc c1 (a_base a) in
        let '(r, c3) := sym_readBIFr segs ss bc kx xc ex lis lia gl c2 scr br e63 a n (amo_sx wd) in
        (match r with
         | None => SStop
         | Some (v, scs, scr', nx') =>
             SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                      (s_log ss) (s_know ss) nx' (Some a)) scs scr'
         end, c3)
      else (SStop, c)
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let '(a, c1) := BASFK.to_saddrKB_c bc c e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              let '(br, c2) := BASFK.base_range_c bc c1 (a_base a) in
              (SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) (ELit 0))
                        (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                   (flat_scBFr br a n ++ storeok_scBF bc ex a n) scr, c2)
            else (SStop, c1)
        | None => (SStop, c1)
        end
      else (SStop, c)
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => (SStop, c)
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let '(a, c1) := BASFK.to_saddrKB_c bc c e 0 in
            match resv_inval (s_resv ss) a with
            | None => (SStop, c1)
            | Some r' =>
                let '(br, e63, c2) := BASFK.base_range63_c bc c1 (a_base a) in
                let '(r, c3) := sym_readBIFr segs ss bc kx xc ex lis lia gl c2 scr br e63 a n (amo_sx wd) in
                (match r with
                 | None => SStop
                 | Some (vold, scs, scr', nx') =>
                     SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) vold)
                              (SE a n (amo_newvalBF bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                         (scs ++ storeok_scBF bc ex a n) scr'
                 end, c3)
            end
          else (SStop, c)
      end
  | _ => (sym_stepBIF bc kx xc ex lis segs i ss scr, c)
  end.

Local Open Scope Z_scope.

Record xme : Type := XME { xe_c : saddr; xe_m : expr; xe_x : xin }.
Record xmb : Type := XMB { xb_b : expr; xb_bi : binf; xb_l : list xme }.
Definition xmemo : Type := list xmb.
Fixpoint xe_find (l : list xme) (cb : expr) (co : Z) (m : expr) : option xin :=
  match l with
  | [] => None
  | e :: r => if (if Z.eqb co (a_off (xe_c e)) then if BASFK.expr_eqbF cb (a_base (xe_c e)) then BASFK.expr_eqbF m (xe_m e) else false else false)
              then Some (xe_x e) else xe_find r cb co m
  end.

Definition nwlit (bc : bctx) (n : Z) : bool := if (if Z.leb 0 n then Z.ltb n two63z else false) then true else lin_nowrapRB bc (ELit n).
Definition xb_eval (bc : bctx) (b : xmb) (k n : Z) (cb : expr) (co : Z) (m : expr) : bool * option xmb :=
  match xe_find (xb_l b) cb co m with
  | Some x => (xeval x k (snorm n) (zlit64 n) (nwlit bc n), None)
  | None => let x := mk_xin bc (xb_b b) (xb_bi b) cb co m in
            (xeval x k (snorm n) (zlit64 n) (nwlit bc n), Some (XMB (xb_b b) (xb_bi b) (XME (SA cb co) m x :: xb_l b)))
  end.
Fixpoint xm_eval (bc : bctx) (xm : xmemo) (b1 : expr) (k n : Z) (cb : expr) (co : Z) (m : expr) : bool * xmemo :=
  match xm with
  | [] => let bi := mk_binf bc b1 in let x := mk_xin bc b1 bi cb co m in
          (xeval x k (snorm n) (zlit64 n) (nwlit bc n), [XMB b1 bi [XME (SA cb co) m x]])
  | b :: r => if BASFK.expr_eqbF b1 (xb_b b) then
                match xb_eval bc b k n cb co m with
                | (v, Some b') => (v, b' :: r)
                | (v, None) => (v, xm)
                end
              else let '(v, r') := xm_eval bc r b1 k n cb co m in (v, b :: r')
  end.
Definition XBOK (bc : bctx) (b : xmb) : Prop :=
  xb_bi b = mk_binf bc (xb_b b) /\ forall e, In e (xb_l b) -> xe_x e = mk_xin bc (xb_b b) (mk_binf bc (xb_b b)) (a_base (xe_c e)) (a_off (xe_c e)) (xe_m e).
Definition XMOK (bc : bctx) (xm : xmemo) : Prop := forall b, In b xm -> XBOK bc b.
Lemma XMOK_nil : forall bc, XMOK bc []. Proof. intros bc b []. Qed.
Lemma nwlit_eq : forall bc n, nwlit bc n = lin_nowrapRB bc (ELit n).
Proof.
  intros bc n. unfold nwlit. destruct (Z.leb_spec 0 n); [|reflexivity]. destruct (Z.ltb_spec n two63z); [|reflexivity].
  symmetry. apply lin_nowrapRB_lit. lia.
Qed.
Lemma xe_find_spec : forall l cb co m x, xe_find l cb co m = Some x -> exists e, In e l /\ xe_x e = x /\ xe_c e = SA cb co /\ xe_m e = m.
Proof.
  induction l as [|e r IH]; intros cb co m x H; [discriminate|]. cbn [xe_find] in H.
  destruct (Z.eqb_spec co (a_off (xe_c e))) as [E1|N1].
  - destruct (BASFK.expr_eqbF cb (a_base (xe_c e))) eqn:E2.
    + destruct (BASFK.expr_eqbF m (xe_m e)) eqn:E3.
      * injection H as <-. apply BASFK.expr_eqbF_true in E2, E3. exists e. split; [left; reflexivity|]. split; [reflexivity|].
        split; [destruct (xe_c e) as [cb' co']; cbn in *; subst; reflexivity|symmetry; exact E3].
      * destruct (IH _ _ _ _ H) as (e' & I & R). exists e'. split; [right; exact I|exact R].
    + destruct (IH _ _ _ _ H) as (e' & I & R). exists e'. split; [right; exact I|exact R].
  - destruct (IH _ _ _ _ H) as (e' & I & R). exists e'. split; [right; exact I|exact R].
Qed.
Lemma xb_eval_spec : forall bc b k n cb co m, XBOK bc b ->
  fst (xb_eval bc b k n cb co m) = xinsideB bc (xb_b b) k (ELit n) cb co m
  /\ match snd (xb_eval bc b k n cb co m) with Some b' => XBOK bc b' /\ xb_b b' = xb_b b | None => True end.
Proof.
  intros bc b k n cb co m [HB HL]. unfold xb_eval. rewrite nwlit_eq.
  destruct (xe_find (xb_l b) cb co m) as [x|] eqn:F; cbn [fst snd].
  - split; [|exact I]. destruct (xe_find_spec _ _ _ _ _ F) as (e & I1 & <- & EC & EM).
    rewrite (HL e I1), EC, EM. cbn [a_base a_off]. apply xeval_eq.
  - rewrite HB. split; [apply xeval_eq|]. split; [|reflexivity]. split; [reflexivity|]. cbn [xb_b xb_l].
    intros e [<-|I1]; [reflexivity|apply HL; exact I1].
Qed.
Lemma xm_eval_spec : forall bc xm b1 k n cb co m, XMOK bc xm ->
  fst (xm_eval bc xm b1 k n cb co m) = xinsideB bc b1 k (ELit n) cb co m /\ XMOK bc (snd (xm_eval bc xm b1 k n cb co m)).
Proof.
  intros bc xm b1 k n cb co m. induction xm as [|b r IH]; intros H.
  - cbn [xm_eval fst snd]. rewrite nwlit_eq. split; [apply xeval_eq|].
    intros b [<-|[]]. split; [reflexivity|]. cbn [xb_b xb_l]. intros e [<-|[]]. reflexivity.
  - cbn [xm_eval]. destruct (BASFK.expr_eqbF b1 (xb_b b)) eqn:E.
    + apply BASFK.expr_eqbF_true in E. subst b1. assert (HB : XBOK bc b) by (apply H; left; reflexivity).
      destruct (xb_eval_spec bc b k n cb co m HB) as [E1 E2]. destruct (xb_eval bc b k n cb co m) as [v [b'|]]; cbn [fst snd] in *.
      * split; [exact E1|]. intros x [<-|I]; [apply E2|apply H; right; exact I].
      * split; [exact E1|exact H].
    + assert (HR : XMOK bc r) by (intros x I; apply H; right; exact I). destruct (IH HR) as [E1 E2].
      destruct (xm_eval bc r b1 k n cb co m) as [v r']. cbn [fst snd] in *. split; [exact E1|].
      intros x [<-|I]; [apply H; left; reflexivity|apply E2; exact I].
Qed.

Definition sub_itvM (bc : bctx) (xm : xmemo) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool * xmemo :=
  if (if (if BASFK.expr_eqbF b (a_base c) then Z.leb (a_off c) k else false) then
        match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then (true, xm)
  else if (if Z.leb 0 n then Z.ltb n two64 else false) then
         (if shares_var b (a_base c) then xm_eval bc xm b k n (a_base c) (a_off c) m
          else (xinsideB bc b k (ELit n) (a_base c) (a_off c) m, xm))
       else (false, xm).
Lemma sub_itvM_spec : forall bc xm b k n c m, XMOK bc xm ->
  fst (sub_itvM bc xm b k n c m) = sub_itvB bc b k n c m /\ XMOK bc (snd (sub_itvM bc xm b k n c m)).
Proof.
  intros bc xm b k n c m H. unfold sub_itvM, sub_itvB. rewrite BASFK.expr_eqbF_eq.
  replace (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool with (if expr_eqb b (a_base c) then Z.leb (a_off c) k else false) by (destruct (expr_eqb b (a_base c)); reflexivity).
  replace (Z.leb 0 n && Z.ltb n two64)%bool with (if Z.leb 0 n then Z.ltb n two64 else false) by (destruct (Z.leb 0 n); reflexivity).
  destruct (if (if expr_eqb b (a_base c) then Z.leb (a_off c) k else false) then match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end else false);
    [split; [reflexivity|exact H]|].
  destruct (if Z.leb 0 n then Z.ltb n two64 else false); [|split; [reflexivity|exact H]].
  destruct (shares_var b (a_base c)); [apply xm_eval_spec; exact H|split; [reflexivity|exact H]].
Qed.
Fixpoint in_sidesM (bc : bctx) (xm : xmemo) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool * xmemo :=
  match D with
  | [] => (false, xm)
  | (c, m) :: r => let '(v, xm') := sub_itvM bc xm b2 k2 n2 c m in if v then (true, xm') else in_sidesM bc xm' r b2 k2 n2
  end.
Lemma in_sidesM_spec : forall bc D xm b2 k2 n2, XMOK bc xm ->
  fst (in_sidesM bc xm D b2 k2 n2) = in_sidesB bc D b2 k2 n2 /\ XMOK bc (snd (in_sidesM bc xm D b2 k2 n2)).
Proof.
  intros bc D. induction D as [|[c m] r IH]; intros xm b2 k2 n2 H; [split; [reflexivity|exact H]|].
  cbn [in_sidesM in_sidesB]. destruct (sub_itvM_spec bc xm b2 k2 n2 c m H) as [E1 E2].
  destruct (sub_itvM bc xm b2 k2 n2 c m) as [v xm']. cbn [fst snd] in *. subst v.
  destruct (sub_itvB bc b2 k2 n2 c m); [split; [reflexivity|exact E2]|apply IH; exact E2].
Qed.
Definition ranges_apartM (bc : bctx) (kd : list kentry) (sp : sprep) (br1 : option (Z * Z)) (xm : xmemo) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool * xmemo :=
  if BASFK.expr_eqbF b2 b1 then ((if Z.leb (k1 + n1) k2 then true else Z.leb (k2 + n2) k1)%Z, xm) else
  if (match br1, sp_rng sp with
      | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + k1 + n1) (lo2 + k2) then true else Z.leb (hi2 + k2 + n2) (lo1 + k1)
      | _, _ => false
      end)%Z then (true, xm)
  else if Z.eqb (zlit64 n2) n2 then
         let '(v, xm') := in_sidesM bc xm (sp_D sp) b1 k1 n1 in
         if v then (true, xm') else (lin_apartB bc b1 k1 n1 b2 k2 n2, xm')
       else ((if kdisj_apartB bc kd b1 k1 n1 b2 k2 n2 then true else lin_apartB bc b1 k1 n1 b2 k2 n2), xm).
Lemma ranges_apartM_spec : forall bc kd sp br1 xm b1 k1 n1 b2 k2 n2, XMOK bc xm ->
  fst (ranges_apartM bc kd sp br1 xm b1 k1 n1 b2 k2 n2) = ranges_apartBF2 bc kd sp br1 b1 k1 n1 b2 k2 n2
  /\ XMOK bc (snd (ranges_apartM bc kd sp br1 xm b1 k1 n1 b2 k2 n2)).
Proof.
  intros bc kd sp br1 xm b1 k1 n1 b2 k2 n2 H. unfold ranges_apartM, ranges_apartBF2.
  destruct (BASFK.expr_eqbF b2 b1); [split; [reflexivity|exact H]|].
  destruct (match br1, sp_rng sp with
            | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + k1 + n1) (lo2 + k2) then true else Z.leb (hi2 + k2 + n2) (lo1 + k1)
            | _, _ => false end)%Z; [split; [reflexivity|exact H]|].
  destruct (Z.eqb (zlit64 n2) n2); [|split; [reflexivity|exact H]].
  destruct (in_sidesM_spec bc (sp_D sp) xm b1 k1 n1 H) as [E1 E2].
  destruct (in_sidesM bc xm (sp_D sp) b1 k1 n1) as [v xm']. cbn [fst snd] in *. subst v.
  destruct (in_sidesB bc (sp_D sp) b1 k1 n1); split; try reflexivity; exact E2.
Qed.
Fixpoint log_lookupBF3M (bc : bctx) (kd : list kentry) (br1 : option (Z * Z)) (ra : option (PrimInt63.int * PrimInt63.int))
         (log : list sentry) (lis : list sprep) (lia : list sann)
         (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (hints : list bool) (acc : list sidecond) (xm : xmemo) : lres * xmemo :=
  match log, lis, lia with
  | [], _, _ => (LMiss acc hints, xm)
  | SE (SA kb kk) w v :: rest, li :: lrest, sa :: arest =>
      match rel_litF rb rk zn kb kk (sa_zw sa) with
      | RInside d => (LHit (mkExt sx (Z.to_nat d) n v) acc hints, xm)
      | RDisjoint => log_lookupBF3M bc kd br1 ra rest lrest arest rb rk n zn sx hints acc xm
      | RPartial => (match log_bytes_lit log rb rk n with
                     | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                     | None => LStuck
                     end, xm)
      | RUnknown =>
          let '(ap, xm') := if i63apart ra (sa_rng sa) then (true, xm) else ranges_apartM bc kd li br1 xm rb rk zn kb kk (sa_zw sa) in
          if ap then log_lookupBF3M bc kd br1 ra rest lrest arest rb rk n zn sx hints acc xm'
          else
          match hints with
          | false :: _ => (LStuck, xm')
          | _ => log_lookupBF3M bc kd br1 ra rest lrest arest rb rk n zn sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) xm'
          end
      end
  | _, _, _ => (log_lookupBF2 bc kd (Some br1) log lis rb rk n sx hints acc, xm)
  end.
Lemma log_lookupBF3M_spec : forall bc kd br1 ra log lis lia rb rk n zn sx hints acc xm, XMOK bc xm ->
  fst (log_lookupBF3M bc kd br1 ra log lis lia rb rk n zn sx hints acc xm) = log_lookupBF3 bc kd br1 ra log lis lia rb rk n zn sx hints acc
  /\ XMOK bc (snd (log_lookupBF3M bc kd br1 ra log lis lia rb rk n zn sx hints acc xm)).
Proof.
  intros bc kd br1 ra log. induction log as [|[[kb kk] w v] rest IH]; intros lis lia rb rk n zn sx hints acc xm H; [split; [reflexivity|exact H]|].
  destruct lis as [|li lrest]; [split; [reflexivity|exact H]|]. destruct lia as [|sa arest]; [split; [reflexivity|exact H]|].
  cbn [log_lookupBF3M log_lookupBF3].
  destruct (rel_litF rb rk zn kb kk (sa_zw sa)); try (split; [reflexivity|exact H]); [apply IH; exact H|].
  destruct (i63apart ra (sa_rng sa)); [apply IH; exact H|].
  destruct (ranges_apartM_spec bc kd li br1 xm rb rk zn kb kk (sa_zw sa) H) as [E1 E2].
  destruct (ranges_apartM bc kd li br1 xm rb rk zn kb kk (sa_zw sa)) as [ap xm']. cbn [fst snd] in *. subst ap.
  destruct (ranges_apartBF2 bc kd li br1 rb rk zn kb kk (sa_zw sa)); [apply IH; exact E2|].
  destruct hints as [|[|] hs]; try (apply IH; exact E2). split; [reflexivity|exact E2].
Qed.
Definition log_lookupGM (bc : bctx) (kd : list kentry) (br1 : option (Z * Z)) (ra : option (PrimInt63.int * PrimInt63.int))
           (gl : list lgroup) (log : list sentry) (lis : list sprep) (lia : list sann)
           (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (hints : list bool) (xm : xmemo) : lres * xmemo :=
  match (if gl_others_apart gl rb ra then grp_scan gl rb rk zn n sx hints else None) with
  | Some r => (r, xm)
  | None => log_lookupBF3M bc kd br1 ra log lis lia rb rk n zn sx hints [] xm
  end.
Lemma log_lookupGM_spec : forall bc kd br1 ra gl log lis lia rb rk n zn sx hints xm, XMOK bc xm ->
  fst (log_lookupGM bc kd br1 ra gl log lis lia rb rk n zn sx hints xm) = log_lookupG bc kd br1 ra gl log lis lia rb rk n zn sx hints
  /\ XMOK bc (snd (log_lookupGM bc kd br1 ra gl log lis lia rb rk n zn sx hints xm)).
Proof.
  intros. unfold log_lookupGM, log_lookupG.
  destruct (if gl_others_apart gl rb ra then grp_scan gl rb rk zn n sx hints else None); [split; [reflexivity|assumption]|].
  apply log_lookupBF3M_spec. assumption.
Qed.

Definition xinsM (bc : bctx) (br : option (Z * Z)) (xm : xmemo) (rb : expr) (rk zn : Z) (kb : expr) (kk : Z) (len : expr) : bool * xmemo :=
  if shares_var rb kb then xm_eval bc xm rb rk zn kb kk len
  else ((if novars kb then xinside_numBr bc br rk (ELit zn) kb kk len else false), xm).
Lemma xinsM_spec : forall bc br xm rb rk zn kb kk len, XMOK bc xm ->
  fst (xinsM bc br xm rb rk zn kb kk len) = xinsideBr bc br rb rk (ELit zn) kb kk len
  /\ XMOK bc (snd (xinsM bc br xm rb rk zn kb kk len)).
Proof.
  intros bc br xm rb rk zn kb kk len H. unfold xinsM, xinsideBr. destruct (shares_var rb kb) eqn:E.
  - destruct (xm_eval_spec bc xm rb rk zn kb kk len H) as [E1 E2]. split; [|exact E2]. rewrite E1. unfold xinsideB. rewrite E. reflexivity.
  - split; [|exact H]. cbn [fst]. destruct (novars kb); [|reflexivity]. destruct (xinside_numBr bc br rk (ELit zn) kb kk len); reflexivity.
Qed.

Definition kstepM (bc : bctx) (st : option (list IMGFK.sgi)) (segs : list Segment) (br : option (Z * Z)) (K : kentry) (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool)
           (acc : list sidecond) (xm : xmemo) : option lres * xmemo :=
  match K with
  | KZero (SA kb kk) len =>
      if (match len with ELit _ => BASFK.expr_eqbF rb kb | _ => false end) then
        (match kstepF bc st segs br K rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => None | r => Some r end, xm)
      else let '(v, xm') := xinsM bc br xm rb rk zn kb kk len in ((if v then Some (LHit (ELit 0) acc []) else None), xm')
  | KFill (SA kb kk) len c =>
      if (match len with ELit _ => BASFK.expr_eqbF rb kb | _ => false end) then
        (match kstepF bc st segs br K rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => None | r => Some r end, xm)
      else let '(v, xm') := xinsM bc br xm rb rk zn kb kk len in ((if v then Some (LHit (fill_lit sx n c) acc []) else None), xm')
  | _ => (match kstepF bc st segs br K rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => None | r => Some r end, xm)
  end.
Lemma kstepF_marker : forall bc st segs br K rb rk n zn sx acc k,
  kstepF bc st segs br K rb rk n zn sx acc k
  = match kstepF bc st segs br K rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => k tt | r => r end.
Proof.
  intros. unfold kstepF.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity;
    repeat match goal with
           | |- context [match ?x with ELit _ => _ | _ => _ end] => is_var x; destruct x
           | |- context [match ?x with Z0 => _ | Zpos _ => _ | Zneg _ => _ end] => is_var x; destruct x
           | |- context [if ?c then _ else _] => lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end
           | |- context [match ?c with Some _ => _ | None => _ end] => lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end
           end; try reflexivity.
Qed.

Lemma kstepM_spec : forall bc st segs br0 K rb rk n zn sx acc xm k, XMOK bc xm ->
  kstepF bc st segs br0 K rb rk n zn sx acc k
  = match fst (kstepM bc st segs br0 K rb rk n zn sx acc xm) with Some r => r | None => k tt end
  /\ XMOK bc (snd (kstepM bc st segs br0 K rb rk n zn sx acc xm)).
Proof.
  intros bc st segs br0 K rb rk n zn sx acc xm k H.
  assert (G : forall K', kstepF bc st segs br0 K' rb rk n zn sx acc k
              = match fst (match kstepF bc st segs br0 K' rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => None | r => Some r end, xm) with
                | Some r => r | None => k tt end
              /\ XMOK bc (snd (match kstepF bc st segs br0 K' rb rk n zn sx acc (fun _ => LMiss [] []) with LMiss _ _ => None | r => Some r end, xm))).
  { intros K'. cbn [fst snd]. split; [|exact H]. rewrite (kstepF_marker bc st segs br0 K' rb rk n zn sx acc k).
    destruct (kstepF bc st segs br0 K' rb rk n zn sx acc (fun _ => LMiss [] [])); reflexivity. }
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try apply G.
  - unfold kstepM. destruct (match len with ELit _ => BASFK.expr_eqbF rb kb | _ => false end) eqn:EL; [apply G|].
    destruct (xinsM_spec bc br0 xm rb rk zn kb kk len H) as [E1 E2].
    destruct (xinsM bc br0 xm rb rk zn kb kk len) as [v xm']. cbn [fst snd] in *. split; [|exact E2].
    unfold kstepF. destruct len; rewrite ?EL, <- ?E1; destruct v; reflexivity.
  - unfold kstepM. destruct (match len with ELit _ => BASFK.expr_eqbF rb kb | _ => false end) eqn:EL; [apply G|].
    destruct (xinsM_spec bc br0 xm rb rk zn kb kk len H) as [E1 E2].
    destruct (xinsM bc br0 xm rb rk zn kb kk len) as [v xm']. cbn [fst snd] in *. split; [|exact E2].
    unfold kstepF. destruct len; rewrite ?EL, <- ?E1; destruct v; reflexivity.
Qed.
Fixpoint kwalkM (bc : bctx) (st : option (list IMGFK.sgi)) (segs : list Segment) (br : option (Z * Z)) (l : list (option (PrimInt63.int * PrimInt63.int) * kentry))
         (r : option (PrimInt63.int * PrimInt63.int)) (rb : expr) (rk : Z) (n : nat) (zn : Z) (sx : bool) (acc : list sidecond) (xm : xmemo) : lres * xmemo :=
  match l with
  | [] => (LMiss acc [], xm)
  | (a, K) :: rest =>
      if (match a, r with
          | Some (s, e), Some (r63, zn63) => if PrimInt63.leb s r63 then PrimInt63.leb (PrimInt63.add r63 zn63) e else false
          | _, _ => true
          end)
      then let '(o, xm') := kstepM bc st segs br K rb rk n zn sx acc xm in
           match o with
           | Some res => (res, xm')
           | None => kwalkM bc st segs br rest r rb rk n zn sx acc xm'
           end
      else kwalkM bc st segs br rest r rb rk n zn sx acc xm
  end.
Lemma kwalkM_spec : forall bc st segs br0 l r rb rk n zn sx acc xm, XMOK bc xm ->
  fst (kwalkM bc st segs br0 l r rb rk n zn sx acc xm) = kwalkfF bc st segs br0 l r rb rk n zn sx acc
  /\ XMOK bc (snd (kwalkM bc st segs br0 l r rb rk n zn sx acc xm)).
Proof.
  intros bc st segs br0 l r rb rk n zn sx acc. induction l as [|[a K] rest IH]; intros xm H; [split; [reflexivity|exact H]|].
  cbn [kwalkM kwalkfF].
  destruct (match a, r with
            | Some (s, e), Some (r63, zn63) => if PrimInt63.leb s r63 then PrimInt63.leb (PrimInt63.add r63 zn63) e else false
            | _, _ => true end); [|apply IH; exact H].
  destruct (kstepM_spec bc st segs br0 K rb rk n zn sx acc xm (fun _ => kwalkfF bc st segs br0 rest r rb rk n zn sx acc) H) as [E1 E2].
  rewrite E1. destruct (kstepM bc st segs br0 K rb rk n zn sx acc xm) as [[res|] xm']; cbn [fst snd] in *.
  - split; [reflexivity|exact E2].
  - apply IH. exact E2.
Qed.

Definition know_lookupA0IM (bc : bctx) (kx : kix) (xc : xctx) (br : option (Z * Z)) (segs : list Segment) (rb : expr) (rk : Z)
           (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) (xm : xmemo) : lres * xmemo :=
  match hints, n with
  | [], S _ =>
      if is_lit0 rb then (know_lookupA0IF bc kx xc br segs rb rk n sx hints acc, xm)
      else let zn := Z.of_nat n in kwalkM bc (xc_st xc) segs br (xc_fw xc) (qann rk zn) rb rk n zn sx acc xm
  | _, _ => (know_lookupA0IF bc kx xc br segs rb rk n sx hints acc, xm)
  end.
Lemma know_lookupA0IM_spec : forall bc kx xc br segs rb rk n sx hints acc xm, XMOK bc xm ->
  fst (know_lookupA0IM bc kx xc br segs rb rk n sx hints acc xm) = know_lookupA0IF bc kx xc br segs rb rk n sx hints acc
  /\ XMOK bc (snd (know_lookupA0IM bc kx xc br segs rb rk n sx hints acc xm)).
Proof.
  intros bc kx xc br segs rb rk n sx hints acc xm H. unfold know_lookupA0IM.
  destruct hints as [|h hs]; [|split; [reflexivity|exact H]]. destruct n as [|n']; [split; [reflexivity|exact H]|].
  destruct (is_lit0 rb) eqn:L; [split; [reflexivity|exact H]|]. cbv zeta.
  destruct (kwalkM_spec bc (xc_st xc) segs br (xc_fw xc) (qann rk (Z.of_nat (S n'))) rb rk (S n') (Z.of_nat (S n')) sx acc xm H) as [E1 E2].
  split; [|exact E2]. rewrite E1. unfold know_lookupA0IF. rewrite L. reflexivity.
Qed.
Definition know_lookupABIM (bc : bctx) (kx : kix) (xc : xctx) (br : option (Z * Z)) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) (xm : xmemo) : lres * xmemo :=
  let '(r0, xm') := know_lookupA0IM bc kx xc br segs rb rk n sx hints acc xm in
  (match r0 with
   | LMiss acc' hints' =>
       match know_bytes_lit segs kn rb rk n with
       | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
       | None => LMiss acc' hints'
       end
   | r => r
   end, xm').
Lemma know_lookupABIM_spec : forall bc kx xc br segs kn rb rk n sx hints acc xm, XMOK bc xm ->
  fst (know_lookupABIM bc kx xc br segs kn rb rk n sx hints acc xm) = know_lookupABIF bc kx xc br segs kn rb rk n sx hints acc
  /\ XMOK bc (snd (know_lookupABIM bc kx xc br segs kn rb rk n sx hints acc xm)).
Proof.
  intros bc kx xc br segs kn rb rk n sx hints acc xm H. unfold know_lookupABIM, know_lookupABIF.
  destruct (know_lookupA0IM_spec bc kx xc br segs rb rk n sx hints acc xm H) as [E1 E2].
  destruct (know_lookupA0IM bc kx xc br segs rb rk n sx hints acc xm) as [r0 xm']. cbn [fst snd] in *. subst r0. split; [|exact E2].
  destruct (know_lookupA0IF bc kx xc br segs rb rk n sx hints acc); reflexivity.
Qed.

Definition sym_readBIFx (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep)
           (lia : list sann) (gl : list lgroup) (c : BASFK.bcache) (xm : xmemo) (scr : scripts)
           (br : option (Z * Z)) (e63 : option (PrimInt63.int * PrimInt63.int)) (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) * BASFK.bcache * xmemo :=
  let zn := Z.of_nat n in
  let ra := rann63 e63 br (a_off a) zn in
  let '(lr, xm0) := log_lookupGM bc (be_kd ex) br ra gl (s_log ss) lis lia (a_base a) (a_off a) n zn sx' (sc_hints scr) xm in
  match lr with
  | LStuck => (None, c, xm0)
  | LHit v scs hints =>
      let '(v', c') := BASFK.foldKB_c bc c (extK0B bc v) in
      (Some (v', flat_scBFa ra br a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss), c', xm0)
  | LMiss scs hints =>
      let '(kr, xm') := know_lookupABIM bc kx xc br segs (s_know ss) (a_base a) (a_off a) n sx' hints scs xm0 in
      match kr with
      | LStuck => (None, c, xm')
      | LHit v scs' hints' =>
          let '(v', c') := BASFK.foldKB_c bc c (extK0B bc v) in
          (Some (v', flat_scBFa ra br a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss), c', xm')
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          (Some (rv, flat_scBFa ra br a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i), c, xm')
      end
  end.
Lemma sym_readBIFx_spec : forall segs ss bc kx xc ex lis lia gl c xm scr br e63 a n sx', XMOK bc xm ->
  fst (sym_readBIFx segs ss bc kx xc ex lis lia gl c xm scr br e63 a n sx') = sym_readBIFr segs ss bc kx xc ex lis lia gl c scr br e63 a n sx'
  /\ XMOK bc (snd (sym_readBIFx segs ss bc kx xc ex lis lia gl c xm scr br e63 a n sx')).
Proof.
  intros segs ss bc kx xc ex lis lia gl c xm scr br e63 a n sx' H. unfold sym_readBIFx, sym_readBIFr. cbv zeta.
  destruct (log_lookupGM_spec bc (be_kd ex) br (rann63 e63 br (a_off a) (Z.of_nat n)) gl (s_log ss) lis lia (a_base a) (a_off a) n (Z.of_nat n) sx' (sc_hints scr) xm H) as [L1 L2].
  destruct (log_lookupGM bc (be_kd ex) br (rann63 e63 br (a_off a) (Z.of_nat n)) gl (s_log ss) lis lia (a_base a) (a_off a) n (Z.of_nat n) sx' (sc_hints scr) xm) as [lr xm0].
  cbn [fst snd] in L1, L2. subst lr.
  destruct (log_lookupG bc (be_kd ex) br (rann63 e63 br (a_off a) (Z.of_nat n)) gl (s_log ss) lis lia (a_base a) (a_off a) n (Z.of_nat n) sx' (sc_hints scr)) as [v scs hints|scs hints|].
  - destruct (BASFK.foldKB_c bc c (extK0B bc v)) as [v' c']. split; [reflexivity|exact L2].
  - destruct (know_lookupABIM_spec bc kx xc br segs (s_know ss) (a_base a) (a_off a) n sx' hints scs xm0 L2) as [E1 E2].
    destruct (know_lookupABIM bc kx xc br segs (s_know ss) (a_base a) (a_off a) n sx' hints scs xm0) as [kr xm']. cbn [fst snd] in *. subst kr.
    destruct (know_lookupABIF bc kx xc br segs (s_know ss) (a_base a) (a_off a) n sx' hints scs) as [v scs' hints'|scs' hints'|].
    + destruct (BASFK.foldKB_c bc c (extK0B bc v)) as [v' c']. split; [reflexivity|exact E2].
    + split; [reflexivity|exact E2].
    + split; [reflexivity|exact E2].
  - split; [reflexivity|exact L2].
Qed.

Definition sym_stepBIF_cx (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (c : BASFK.bcache) (xm : xmemo) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres * BASFK.bcache * xmemo :=
  match i with
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      let sx' := match sz with SZ8 => false | _ => sx end in
      let '(a, c1) := BASFK.to_saddrKB_c bc c (sr_getF (s_regs ss) rs) (bv_signedF imm) in
      let '(br, e63, c2) := BASFK.base_range63_c bc c1 (a_base a) in
      let '(r, c3, xm') := sym_readBIFx segs ss bc kx xc ex lis lia gl c2 xm scr br e63 a n sx' in
      (match r with
       | None => SStop
       | Some (v, scs, scr', nx') =>
           SOk (SSR (s_pc ss + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                    (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
       end, c3, xm')
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := sr_getF (s_regs ss) rs in
      if amo_alignedbB bc e wd then
        let '(a, c1) := BASFK.to_saddrKB_c bc c e 0 in
        let '(br, e63, c2) := BASFK.base_range63_c bc c1 (a_base a) in
        let '(r, c3, xm') := sym_readBIFx segs ss bc kx xc ex lis lia gl c2 xm scr br e63 a n (amo_sx wd) in
        (match r with
         | None => SStop
         | Some (v, scs, scr', nx') =>
             SOk (SSR (s_pc ss + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridxF rd) v)
                      (s_log ss) (s_know ss) nx' (Some a)) scs scr'
         end, c3, xm')
      else (SStop, c, xm)
  | _ => (sym_stepBIF_c bc kx xc ex lis lia gl c segs i ss scr, xm)
  end.
Lemma sym_stepBIF_cx_spec : forall bc kx xc ex lis lia gl c xm segs i ss scr, XMOK bc xm ->
  fst (sym_stepBIF_cx bc kx xc ex lis lia gl c xm segs i ss scr) = sym_stepBIF_c bc kx xc ex lis lia gl c segs i ss scr
  /\ XMOK bc (snd (sym_stepBIF_cx bc kx xc ex lis lia gl c xm segs i ss scr)).
Proof.
  intros bc kx xc ex lis lia gl c xm segs i ss scr H. destruct i; try (split; [reflexivity|exact H]);
  cbn [sym_stepBIF_cx sym_stepBIF_c]; cbv zeta;
  try match goal with |- context [if amo_alignedbB ?bc ?e ?wd then _ else _] => destruct (amo_alignedbB bc e wd); [|split; [reflexivity|exact H]] end;
  match goal with |- context [BASFK.to_saddrKB_c ?bc ?c ?e ?im] => destruct (BASFK.to_saddrKB_c bc c e im) as [a c1] end;
  destruct (BASFK.base_range63_c bc c1 (a_base a)) as [[br e63] c2];
  match goal with |- context [sym_readBIFx ?segs ?ss ?bc ?kx ?xc ?ex ?lis ?lia ?gl ?c2 ?xm ?scr ?br ?e63 ?a ?n ?sx'] =>
    destruct (sym_readBIFx_spec segs ss bc kx xc ex lis lia gl c2 xm scr br e63 a n sx' H) as [E1 E2];
    destruct (sym_readBIFx segs ss bc kx xc ex lis lia gl c2 xm scr br e63 a n sx') as [[r c3] xm'] end;
  cbn [fst snd] in *; rewrite <- E1; (split; [reflexivity|exact E2]).
Qed.

Definition sym_stepBIF_cr (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (c : BASFK.bcache) (xm : xmemo) (rm : BASFK.rmemo) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts)
  : stepres * BASFK.bcache * xmemo * BASFK.rmemo :=
  let g r := sr_getF (s_regs ss) r in
  let p := s_pc ss in
  let dflt := fun (_ : unit) => (sym_stepBIF_cx bc kx xc ex lis lia gl c xm segs i ss scr, rm) in
  let big2 := fun (a b : expr) => if BASFK.bigE a then true else BASFK.bigE b in
  match i with
  | OpImm op rd rs imm =>
      if BASFK.bigE (g rs) then
        let '(v, rm') := BASFK.foldKBM bc rm (mkAluK0BF bc op (g rs) (ELit (bv_signedF imm))) in (SOk (ssetF ss rd v (p + 4)) [] scr, c, xm, rm')
      else dflt tt
  | ShiftImm op rd rs sh =>
      if BASFK.bigE (g rs) then
        let '(v, rm') := BASFK.foldKBM bc rm (mkAluK0BF bc op (g rs) (ELit (bv_unsigned sh))) in (SOk (ssetF ss rd v (p + 4)) [] scr, c, xm, rm')
      else dflt tt
  | Op op rd rs1 rs2 =>
      if big2 (g rs1) (g rs2) then
        let '(v, rm') := BASFK.foldKBM bc rm (mkAluK0BF bc op (g rs1) (g rs2)) in (SOk (ssetF ss rd v (p + 4)) [] scr, c, xm, rm')
      else dflt tt
  | OpImm32 rd rs imm =>
      if BASFK.bigE (g rs) then
        let '(v, rm') := BASFK.foldKBM bc rm (mkAluwK0BF bc ALU_ADD (g rs) (ELit (bv_signedF imm))) in (SOk (ssetF ss rd v (p + 4)) [] scr, c, xm, rm')
      else dflt tt
  | Op32 op rd rs1 rs2 =>
      if big2 (g rs1) (g rs2) then
        let '(v, rm') := BASFK.foldKBM bc rm (mkAluwK0BF bc op (g rs1) (g rs2)) in (SOk (ssetF ss rd v (p + 4)) [] scr, c, xm, rm')
      else dflt tt
  | _ => dflt tt
  end.

Local Close Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Fixpoint existsbL {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | a :: r => if f a then true else existsbL f r end.
Definition zf_coversBF (bc : bctx) (rb : expr) (rk : Z) (zn : Z) (kb : expr) (kk : Z) (len : expr) : bool :=
  if (match len with
      | ELit l0 => match rel_litF rb rk zn kb kk (zmod64 l0) with RInside _ => true | _ => false end
      | _ => false
      end) then true
  else xinsideB bc rb rk (ELit zn) kb kk len.
Definition kentry_overlayBF (bc : bctx) (rb : expr) (rk : Z) (zn : Z) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ => zf_coversBF bc rb rk zn kb kk len
  | _ => false
  end.
Definition kentry_readableBF (bc : bctx) (rb : expr) (rk : Z) (zn : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ => match rel_litF rb rk zn kb kk (Z.of_nat w) with RInside _ => true | _ => false end
  | _ => kentry_overlayBF bc rb rk zn K
  end.
Definition kn_readableBF (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  if existsbL (kentry_readableBF bc rb rk (Z.of_nat n)) kn then true else know_bytes_cov segs true kn rb rk n.
Definition kn_overlayBF (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  if existsbL (kentry_overlayBF bc rb rk (Z.of_nat n)) kn then true else know_bytes_cov segs false kn rb rk n.
Definition x_dischargeableBF (bc : bctx) (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  let kn := s_know ss in
  match sc with
  | SCReadBase a n sx (EVar j) =>
      if (match rb with
          | Some (a', n', sx') => if saddr_eqb a' a then if Nat.eqb n' n then Bool.eqb sx' sx else false else false
          | None => false
          end)
      then if Nat.eqb j (s_next ss) then if Nat.ltb j (s_next ss') then if evars_lt (s_next ss) (a_base a) then
           if Nat.leb 1 n then if Nat.leb n 8 then kn_readableBF bc kn (a_base a) (a_off a) n else false else false else false else false else false
      else false
  | SCFlat a (ELit z) =>
      if Z.leb 1 z then if Z.leb z 8 then kn_readableBF bc kn (a_base a) (a_off a) (Z.to_nat z) else false else false
  | SCStoreOk a n => if Nat.leb 1 n then if Nat.leb n 8 then kn_overlayBF bc kn (a_base a) (a_off a) n else false else false
  | _ => false
  end.
Definition x_filterBF (bc : bctx) (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
  match scs with
  | [] => []
  | _ => let rb := find_readbase (s_next ss) scs in
         List.filter (fun sc => negb (x_dischargeableBF bc ss ss' rb sc)) scs
  end.

Definition sym_stepXBIF (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (c : BASFK.bcache) (K : nat) (i : instr) (ss : sym_state) (scr : scripts)
  : stepres * BASFK.bcache :=
  let '(r, c') := sym_stepBIF_c bc kx xc ex lis lia gl c segs i ss scr in
  (match r with
   | SOk ss' scs scr' => SOk (cap_rd K i ss') (x_filterBF bc ss ss' scs) scr'
   | SStop => SStop
   end, c').

Definition sym_stepXBIFx (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (c : BASFK.bcache) (xm : xmemo) (rm : BASFK.rmemo) (K : nat) (i : instr) (ss : sym_state) (scr : scripts)
  : stepres * BASFK.bcache * xmemo * BASFK.rmemo :=
  let '(r, c', xm', rm') := sym_stepBIF_cr bc kx xc ex lis lia gl c xm rm segs i ss scr in
  (match r with
   | SOk ss' scs scr' => SOk (cap_rd K i ss') (x_filterBF bc ss ss' scs) scr'
   | SStop => SStop
   end, c', xm', rm').

Fixpoint mk_stt (stops : list Z) : ptree unit :=
  match stops with
  | [] => PTLeaf
  | z :: r => match z with Zpos p => pt_set p tt (mk_stt r) | _ => mk_stt r end
  end.
Definition is_stopF (stt : ptree unit) (stops : list Z) (pc : Z) : bool :=
  match pc with
  | Zpos p => match pt_get stt p with Some _ => true | None => false end
  | _ => existsb (Z.eqb pc) stops
  end.
Definition is_store_instr (i : instr) : bool :=
  match i with Store _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ => true | _ => false end.

Definition lupd (bc : bctx) (ex : bext) (i : instr) (ss' : sym_state) (lis : list sprep) (lia : list sann) (gl : list lgroup)
           (wc : wcache) : list sprep * list sann * list lgroup * wcache :=
  if is_store_instr i then
    match s_log ss' with
    | e :: _ => let '(sp, wc') := mk_sctx_c bc ex wc e in
                let sa := sann_sp sp e in
                (sp :: lis, sa :: lia, gl_adde gl e sa, wc')
    | [] => (lis, lia, gl, wc)
    end
  else (lis, lia, gl, wc).

Fixpoint sym_execTXBIF_go (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state)
  (lis : list sprep) (lia : list sann) (gl : list lgroup) (ck : sym_state) (cklis : list sprep)
  (cklia : list sann) (ckgl : list lgroup) (wc : wcache) (c : BASFK.bcache) (xm : xmemo) (rm : BASFK.rmemo) (stt : ptree unit) : sym_state * list sprep :=
  match fuel with
  | O => if s_clean ss then (ss, lis) else (ck, cklis)
  | S f =>
      if (if first then false else is_stopF stt stops (s_pc ss)) then (if s_clean ss then (ss, lis) else (ck, cklis)) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then (ss, lis) else (ck, cklis)
      | Some i =>
          let '(r, c', xm', rm') := sym_stepXBIFx bc kx xc ex lis lia gl c xm rm K i ss scr_nil in
          match r with
          | SOk ss' [] _ =>
              if is_store_instr i then
                let '(lis', lia', gl', wc') := lupd bc ex i ss' lis lia gl wc in
                if s_clean ss' then sym_execTXBIF_go bc kx xc ex t K f false stops ss' lis' lia' gl' ss' lis' lia' gl' wc' c' xm' rm' stt
                else sym_execTXBIF_go bc kx xc ex t K f false stops ss' lis' lia' gl' ck cklis cklia ckgl wc' c' xm' rm' stt
              else
                if s_clean ss' then sym_execTXBIF_go bc kx xc ex t K f false stops ss' lis lia gl ss' lis lia gl wc c' xm' rm' stt
                else sym_execTXBIF_go bc kx xc ex t K f false stops ss' lis lia gl ck cklis cklia ckgl wc c' xm' rm' stt
          | _ => if s_clean ss then (ss, lis) else (ck, cklis)
          end
      end
  end.
Definition sym_execTXBIF (bc : bctx) (kx : kix) (xc : xctx) (ex : bext) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state * list sprep :=
  let lis := map (mk_sctx bc ex) (s_log ss) in
  let lia := map (fun e => sann_sp (mk_sctx bc ex e) e) (s_log ss) in
  let gl := GLof (mk_sctx bc ex) (s_log ss) in
  sym_execTXBIF_go bc kx xc ex t K fuel first stops (clr ss) lis lia gl (clr ss) lis lia gl wc_empty [] [] [] (mk_stt stops).

Definition needs_kx (i : instr) : bool :=
  match i with Load _ _ _ _ _ | Lr _ _ _ _ _ | Amo _ _ _ _ _ _ _ => true | _ => false end.
Definition kx_nil : kix := KX [] [] PTLeaf [].
Definition xc_nil : xctx := XC None [] [].
Fixpoint sym_execTXBIF_goL (bc : bctx) (kn : list kentry) (okx : option (kix * xctx)) (ex : bext) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state)
  (lis : list sprep) (lia : list sann) (gl : list lgroup) (ck : sym_state) (cklis : list sprep)
  (cklia : list sann) (ckgl : list lgroup) (wc : wcache) (c : BASFK.bcache) (xm : xmemo) (rm : BASFK.rmemo) (stt : ptree unit) : sym_state * list sprep :=
  match fuel with
  | O => if s_clean ss then (ss, lis) else (ck, cklis)
  | S f =>
      if (if first then false else is_stopF stt stops (s_pc ss)) then (if s_clean ss then (ss, lis) else (ck, cklis)) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then (ss, lis) else (ck, cklis)
      | Some i =>
          let '(kx, xc, okx') :=
            if needs_kx i then
              match okx with
              | Some (kx, xc) => (kx, xc, okx)
              | None => let kx := BLKFK.mk_kix_f kn in let xc := mk_xc segs kx in (kx, xc, Some (kx, xc))
              end
            else (kx_nil, xc_nil, okx) in
          let '(r, c', xm', rm') := sym_stepXBIFx bc kx xc ex lis lia gl c xm rm K i ss scr_nil in
          match r with
          | SOk ss' [] _ =>
              if is_store_instr i then
                let '(lis', lia', gl', wc') := lupd bc ex i ss' lis lia gl wc in
                if s_clean ss' then sym_execTXBIF_goL bc kn okx' ex t K f false stops ss' lis' lia' gl' ss' lis' lia' gl' wc' c' xm' rm' stt
                else sym_execTXBIF_goL bc kn okx' ex t K f false stops ss' lis' lia' gl' ck cklis cklia ckgl wc' c' xm' rm' stt
              else
                if s_clean ss' then sym_execTXBIF_goL bc kn okx' ex t K f false stops ss' lis lia gl ss' lis lia gl wc c' xm' rm' stt
                else sym_execTXBIF_goL bc kn okx' ex t K f false stops ss' lis lia gl ck cklis cklia ckgl wc c' xm' rm' stt
          | _ => if s_clean ss then (ss, lis) else (ck, cklis)
          end
      end
  end.
Definition sym_execTXBIFL (bc : bctx) (kn : list kentry) (ex : bext) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state * list sprep :=
  let lis := map (mk_sctx bc ex) (s_log ss) in
  let lia := map (fun e => sann_sp (mk_sctx bc ex e) e) (s_log ss) in
  let gl := GLof (mk_sctx bc ex) (s_log ss) in
  sym_execTXBIF_goL bc kn None ex t K fuel first stops (clr ss) lis lia gl (clr ss) lis lia gl wc_empty [] [] [] (mk_stt stops).

End WithSegs.

Import APCK.
Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable nx0 : nat.
Definition run_block_f (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if BLKFK.fresh_ok_f nx0 cs then
    let ss := a_ss cs in
    let bc := BLKFK.mkbc_m (facts_of (s_know ss)) in
    let '(ss', scs) := sym_execTXBIFL segs bc (s_know ss) (mk_bext bc) IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carryKF_ctx bc (s_log ss') scs (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
Definition run_block_gc_f (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block_f K fuel stops cs with Some cs' => Some (BLKFK.cs_gc_b nx0 cs') | None => None end.
End WithSegs.

Ltac fe := repeat (apply functional_extensionality; intros ?).

Ltac eqf := rewrite ?BASFK.expr_eqbF_eq in *.
Lemma rel_litF_eq : forall rb rk rn kb kk kn, rel_litF rb rk rn kb kk kn = rel_lit rb rk rn kb kk kn.
Proof. intros. unfold rel_litF, rel_lit. rewrite BASFK.expr_eqbF_eq. reflexivity. Qed.
Lemma rel_litF_fe : rel_litF = rel_lit.
Proof. repeat (apply functional_extensionality; intros ?). apply rel_litF_eq. Qed.
Lemma zmod64_fe : zmod64 = fun z => (z mod 2 ^ 64)%Z.
Proof. fe. apply zmod64_eq. Qed.

Lemma img_fe : forall segs, IMGFK.img_bytesFF (IMGFK.mk_stab segs) segs = img_bytes segs.
Proof. intros. fe. apply IMGFK.img_bytesFF_eq. Qed.

Ltac crush0 :=
  repeat (first [ reflexivity
                | match goal with
                  | |- context [match ?x with ELit _ => _ | _ => _ end] => is_var x; destruct x
                  | |- context [if ?c then _ else _] =>
                      lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end
                  end ]).
Lemma know_lookupA0F_eq : forall bc segs kn rb rk n sx,
  know_lookupA0F bc (IMGFK.mk_stab segs) segs kn rb rk n (Z.of_nat n) sx = know_lookupA0B bc segs kn rb rk n sx.
Proof.
  intros bc segs kn rb rk n sx. induction kn as [|K rest IH]; fe; [reflexivity|].
  cbn [know_lookupA0F know_lookupA0B]. rewrite IH, (img_fe segs), zmod64_fe, BASFK.expr_eqbF_fe. unfold rel_lit, elen. cbv [andb orb]. cbv zeta beta.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity;
    crush0.
Qed.

Lemma xinsideBr_eq : forall bc b1 k1 n1 b2 k2 n2, xinsideBr bc (base_rangeB bc b1) b1 k1 n1 b2 k2 n2 = xinsideB bc b1 k1 n1 b2 k2 n2.
Proof. reflexivity. Qed.
Lemma kstepF_eq : forall bc st segs K rest rb rk n zn sx acc,
  kstepF bc st segs (base_rangeB bc rb) K rb rk n zn sx acc (fun _ => know_lookupA0F bc st segs rest rb rk n zn sx [] acc)
  = know_lookupA0F bc st segs (K :: rest) rb rk n zn sx [] acc.
Proof.
  intros. cbn [know_lookupA0F]. unfold kstepF. rewrite ?xinsideBr_eq.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity;
    destruct len; reflexivity.
Qed.
Local Open Scope Z_scope.
Lemma wB63 : Uint63.wB = 2 ^ 63. Proof. reflexivity. Qed.
Lemma zb_spec : forall z a, zb z = Some a -> Uint63.to_Z a = z + 2 ^ 61 /\ - 2 ^ 60 < z < 2 ^ 60.
Proof. exact BASFK.zb_spec. Qed.

Lemma skipw : forall bc st segs K rest rb rk n zn sx acc s e r63 zn63,
  annw K = Some (s, e) -> zb rk = Some r63 -> IMGFK.z61 zn = Some zn63 ->
  (if PrimInt63.leb s r63 then PrimInt63.leb (PrimInt63.add r63 zn63) e else false) = false ->
  know_lookupA0F bc st segs (K :: rest) rb rk n zn sx [] acc = know_lookupA0F bc st segs rest rb rk n zn sx [] acc.
Proof.
  intros bc st segs K rest rb rk n zn sx acc s e r63 zn63 HA Hr Hz HT.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e0 m|e0 lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; cbn [annw] in HA; try discriminate.
  destruct (zb kk) as [s0|] eqn:Es; [|discriminate]. destruct (IMGFK.z61 (Z.of_nat w)) as [w63|] eqn:Ew; [|discriminate].
  injection HA as <- <-.
  destruct (zb_spec _ _ Es) as [S1 S2]. destruct (zb_spec _ _ Hr) as [R1 R2].
  destruct (IMGFK.z61_spec _ _ Ew) as [W1 W2]. destruct (IMGFK.z61_spec _ _ Hz) as [Z1 Z2].
  rewrite !IMGFK.leb_b in HT. rewrite !Uint63.add_spec, S1, R1, W1, Z1, wB63 in HT.
  rewrite !Z.mod_small in HT by lia.
  cbn [know_lookupA0F]. destruct (BASFK.expr_eqbF rb kb); [|reflexivity].
  destruct (Z.leb_spec kk rk) as [H1|H1].
  - destruct (Z.leb_spec (kk + 2 ^ 61) (rk + 2 ^ 61)) as [_|C]; [|lia].
    destruct (Z.leb_spec (rk + zn) (kk + Z.of_nat w)) as [H2|H2]; [|reflexivity].
    destruct (Z.leb_spec (rk + 2 ^ 61 + zn) (kk + 2 ^ 61 + Z.of_nat w)) as [_|C]; [discriminate|lia].
  - reflexivity.
Qed.
Local Close Scope Z_scope.
Lemma kwalkfF_eq : forall bc st segs l rb rk n zn sx acc,
  kwalkfF bc st segs (base_rangeB bc rb) (map (fun K => (annw K, K)) l) (qann rk zn) rb rk n zn sx acc = know_lookupA0F bc st segs l rb rk n zn sx [] acc.
Proof.
  intros bc st segs l rb rk n zn sx acc. induction l as [|K rest IH]; [reflexivity|].
  cbn [map kwalkfF]. rewrite IH.
  destruct (match annw K, qann rk zn with
            | Some (s, e), Some (r63, zn63) => if PrimInt63.leb s r63 then PrimInt63.leb (PrimInt63.add r63 zn63) e else false
            | _, _ => true end) eqn:HT.
  - apply kstepF_eq.
  - destruct (annw K) as [[s e]|] eqn:HA; [|discriminate]. unfold qann in HT.
    destruct (zb rk) as [r63|] eqn:Hr; [|discriminate]. destruct (IMGFK.z61 zn) as [zn63|] eqn:Hz; [|discriminate].
    symmetry. apply (skipw bc st segs K rest rb rk n zn sx acc s e r63 zn63 HA Hr Hz HT).
Qed.

Definition KXOK (kx : kix) : Prop := exists kn, kx = mk_kix kn.
Lemma mentions_var_lit : forall v z, mentions_var v (ELit z) = false. Proof. reflexivity. Qed.
Lemma shares_var_lit : forall z e, shares_var (ELit z) e = false.
Proof.
  intros z e. induction e as [| | op a IHa b IHb| op a IHa b IHb| op a IHa b IHb| op a IHa b IHb| sx lo n a IHa| sx k i n]; cbn [shares_var]; try reflexivity;
    try (rewrite IHa, IHb; reflexivity). exact IHa.
Qed.
Lemma novars_false_neq_lit : forall kb z, novars kb = false -> expr_eqb (ELit z) kb = false.
Proof. intros kb z H. destruct kb; try reflexivity. discriminate. Qed.
Lemma xinsideB_lit_novars : forall bc z k1 n1 b2 k2 n2, novars b2 = false -> xinsideB bc (ELit z) k1 n1 b2 k2 n2 = false.
Proof. intros. unfold xinsideB. rewrite shares_var_lit, H. reflexivity. Qed.
Lemma skipL : forall bc segs K rest rk n sx acc, keepL K = false ->
  know_lookupA0B bc segs (K :: rest) (ELit 0) rk n sx [] acc = know_lookupA0B bc segs rest (ELit 0) rk n sx [] acc.
Proof.
  intros bc segs K rest rk n sx acc HK. cbn [know_lookupA0B].
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; cbn [keepL] in HK; try discriminate.
  - destruct len; rewrite ?(rel_lit_other _ _ _ _ _ _ (novars_false_neq_lit kb 0 HK)), ?(xinsideB_lit_novars bc 0 rk _ kb kk _ HK); reflexivity.
  - cbv zeta. destruct len; rewrite ?(rel_lit_other _ _ _ _ _ _ (novars_false_neq_lit kb 0 HK)), ?(xinsideB_lit_novars bc 0 rk _ kb kk _ HK); reflexivity.
Qed.
Lemma walk_filter_keepL : forall bc segs (P : kentry -> bool) kn rk n sx acc,
  know_lookupA0B bc segs (List.filter (fun K => P K && keepL K) kn) (ELit 0) rk n sx [] acc
  = know_lookupA0B bc segs (List.filter P kn) (ELit 0) rk n sx [] acc.
Proof.
  intros bc segs P kn rk n sx. induction kn as [|K rest IH]; intros acc; [reflexivity|]. cbn [List.filter].
  destruct (P K); cbn [andb]; [|apply IH].
  destruct (keepL K) eqn:HK.
  - cbn [know_lookupA0B]. rewrite !IH. reflexivity.
  - rewrite (skipL bc segs K _ rk n sx acc HK). apply IH.
Qed.
Lemma filter_filter' : forall (A : Type) (f g : A -> bool) l, List.filter f (List.filter g l) = List.filter (fun x => g x && f x) l.
Proof.
  intros A f g l. induction l as [|x r IH]; [reflexivity|]. cbn [List.filter]. destruct (g x); cbn [andb List.filter]; [|exact IH].
  destruct (f x); rewrite IH; reflexivity.
Qed.
Lemma narrow_keepL : forall g K, narrow_in g K = true -> keepL K = true.
Proof.
  intros g K H. unfold narrow_in in H. destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity;
    cbn [lit0_extent keepL] in *; destruct kb as [z| | | | | | |]; try discriminate; reflexivity.
Qed.
Lemma lit_select_eq : forall bc segs kn rk n sx acc,
  know_lookupA0B bc segs (kx_merge (kx_bucket (kx_gran (mk_kix kn)) (gran rk)) (List.filter (fun t => keepL (snd t)) (kx_w0 (mk_kix kn)))) (ELit 0) rk n sx [] acc
  = know_lookupA0B bc segs (kx_select (mk_kix kn) (ELit 0) rk) (ELit 0) rk n sx [] acc.
Proof.
  intros bc segs kn rk n sx acc. rewrite kx_select_eq. cbn [is_lit0].
  unfold mk_kix. destruct (kx_build kn 1%positive) as [[w0 gr] wf] eqn:Hb. cbn [kx_gran kx_w0 kx_wf fst snd].
  destruct (kx_build_spec kn 1%positive w0 gr wf Hb) as (A & B & C).
  rewrite B, A, filter_filter'.
  rewrite (kx_merge_filters (narrow_in (gran rk)) (fun K => kx_wide0 K && keepL K) kn 1%positive).
  2:{ intros K HK. rewrite (narrow_not_wide (gran rk) K HK). reflexivity. }
  rewrite <- (walk_filter_keepL bc segs (kx_cand0 (gran rk))).
  f_equal. apply filter_ext. intros K. rewrite kx_cand0_split.
  destruct (narrow_in (gran rk) K) eqn:HN; cbn [orb andb]; [rewrite (narrow_keepL _ _ HN); reflexivity|reflexivity].
Qed.
Lemma know_lookupA0IF_eq : forall bc kx segs rb, KXOK kx -> know_lookupA0IF bc kx (mk_xc segs kx) (base_rangeB bc rb) segs rb = know_lookupA0I bc kx segs rb.
Proof.
  intros bc kx segs rb [kn0 ->]. apply functional_extensionality; intros rk.
  apply functional_extensionality; intros n. apply functional_extensionality; intros sx.
  apply functional_extensionality; intros hints. apply functional_extensionality; intros acc.
  unfold know_lookupA0IF, know_lookupA0I, mk_xc. cbn [xc_st xc_fw xc_w0].
  destruct hints as [|h hs]; [|rewrite know_lookupA0F_eq; reflexivity]. destruct n as [|n']; [rewrite know_lookupA0F_eq; reflexivity|].
  destruct (is_lit0 rb) eqn:L.
  - rewrite know_lookupA0F_eq. apply is_lit0_true in L. subst rb. apply lit_select_eq.
  - cbv zeta. rewrite kwalkfF_eq, know_lookupA0F_eq. unfold kx_select. rewrite L. reflexivity.
Qed.
Lemma know_lookupABIF_eq : forall bc kx segs kn rb, KXOK kx -> know_lookupABIF bc kx (mk_xc segs kx) (base_rangeB bc rb) segs kn rb = know_lookupABI bc kx segs kn rb.
Proof. intros bc kx segs kn rb HK. fe. unfold know_lookupABIF, know_lookupABI. rewrite (know_lookupA0IF_eq bc kx segs rb HK). reflexivity. Qed.
Lemma ctz_fuelF_eq : forall f z, ctz_fuelF f z = ctz_fuel f z.
Proof.
  intros f. induction f as [|f IH]; intros z; [reflexivity|]. cbn [ctz_fuelF ctz_fuel].
  rewrite IH, Zmod_odd, <- Z.div2_div. destruct (Z.odd z); reflexivity.
Qed.
Lemma ctz64F_fe : ctz64F = ctz64.
Proof. fe. unfold ctz64F, ctz64. apply ctz_fuelF_eq. Qed.
Lemma ealign0F_eq : forall kn e, ealign0F kn e = ealign0 kn e.
Proof.
  intros kn e. induction e; cbn [ealign0F ealign0]; rewrite ?ctz64F_fe, ?zmod64_eq2; try reflexivity; rewrite ?IHe1, ?IHe2; reflexivity.
Qed.
Lemma ealignBF_eq : ealignBF = ealignB.
Proof. fe. unfold ealignBF, ealignB. rewrite ealign0F_eq. reflexivity. Qed.
Lemma p2_eq : forall j, p2 j = (2 ^ j)%Z.
Proof. intros j. unfold p2. destruct (Z.leb_spec 0 j) as [H|H]; [apply Z.shiftl_1_l|reflexivity]. Qed.
Lemma p2_fe : p2 = fun j => (2 ^ j)%Z.
Proof. apply functional_extensionality; intros j. apply p2_eq. Qed.
Lemma narrow_maskBF_eq : narrow_maskBF = narrow_maskB.
Proof.
  fe. unfold narrow_maskBF, narrow_maskB. rewrite ctz64F_fe, p2_fe. cbv zeta beta.
  destruct (Z.ltb 0 x1); cbn [andb]; [|reflexivity].
  destruct (Z.eqb (x1 + 2 ^ ctz64 x1) (2 ^ Z.log2 (x1 + 2 ^ ctz64 x1))); reflexivity.
Qed.
Lemma modp2_eq : forall x j, modp2 x j = (x mod 2 ^ j)%Z.
Proof. intros x j. unfold modp2. destruct (Z.leb_spec 0 j) as [H|H]; [apply Z.land_ones; exact H|reflexivity]. Qed.
Lemma modp2_fe : modp2 = fun x j => (x mod 2 ^ j)%Z.
Proof. apply functional_extensionality; intros x. apply functional_extensionality; intros j. apply modp2_eq. Qed.
Lemma lowbitsBF_eq : forall bc e j, lowbitsBF bc e j = lowbitsB bc e j.
Proof.
  intros bc e j. induction e; cbn [lowbitsBF lowbitsB]; cbv zeta; rewrite ?ealignBF_eq, ?modp2_fe, ?zmod64_fe; cbv beta; try reflexivity.
  - destruct op; try reflexivity; rewrite ?IHe1, ?IHe2; try reflexivity; destruct e2; reflexivity.
  - destruct op; try reflexivity. destruct e1; try reflexivity. rewrite ?IHe2. reflexivity.
Qed.
Lemma lowbitsBF_fe : lowbitsBF = lowbitsB.
Proof. fe. apply lowbitsBF_eq. Qed.
Lemma lin_nowrapBF_eq : lin_nowrapBF = lin_nowrapB.
Proof. fe. unfold lin_nowrapBF, lin_nowrapB. rewrite BASFK.erangeBF_fe. reflexivity. Qed.
Lemma lin_nowrap_lBF_eq : lin_nowrap_lBF = lin_nowrap_lB.
Proof. fe. unfold lin_nowrap_lBF, lin_nowrap_lB. rewrite BASFK.erangeBF_fe. reflexivity. Qed.
Lemma mkSrlBF_eq : mkSrlBF = mkSrlB.
Proof.
  fe. unfold mkSrlBF, mkSrlB. rewrite lin_nowrapBF_eq, lin_nowrap_lBF_eq, BASFK.erangeBF_fe. cbv zeta.
  destruct (lin_trivial (lin_of x0)); cbn [negb andb]; [reflexivity|].
  destruct (coeffs_div (2 ^ x1) (snd (lin_of x0))); destruct (lin_nowrapB x x0); reflexivity.
Qed.
Lemma mkAnd0BF_eq : mkAnd0BF = mkAnd0B.
Proof.
  fe. unfold mkAnd0BF, mkAnd0B. rewrite mkSrlBF_eq, ealignBF_eq, lowbitsBF_fe, p2_fe. destruct x1; try reflexivity. rewrite zmod64_eq2. cbv zeta beta.
  destruct (Z.eqb (two64 - z mod 2 ^ 64) (2 ^ Z.log2 (two64 - z mod 2 ^ 64))); cbn [andb].
  - reflexivity.
  - destruct (Z.eqb (z mod 2 ^ 64 + 1) (2 ^ Z.log2 (z mod 2 ^ 64 + 1))); reflexivity.
Qed.
Lemma mkAndBF_eq : mkAndBF = mkAndB.
Proof. fe. unfold mkAndBF, mkAndB. rewrite narrow_maskBF_eq, mkAnd0BF_eq. destruct x1; try reflexivity. rewrite zmod64_eq2. reflexivity. Qed.
Lemma mkAndKBF_eq : mkAndKBF = mkAndKB.
Proof. fe. unfold mkAndKBF, mkAndKB. rewrite mkAndBF_eq, !zmod64_fe. reflexivity. Qed.
Lemma mkAluL_fe : BASFK.mkAluL = mkAlu.
Proof. fe. apply BASFK.mkAluL_eq. Qed.
Lemma or_disjointBF_eq : or_disjointBF = or_disjointB.
Proof. fe. unfold or_disjointBF, or_disjointB. rewrite BASFK.erangeBF_fe, ealignBF_eq. reflexivity. Qed.
Lemma mkOrBF_eq : mkOrBF = mkOrB.
Proof. fe. unfold mkOrBF, mkOrB. rewrite or_disjointBF_eq, mkAndKBF_eq. reflexivity. Qed.
Lemma mkAluK0BF_eq : mkAluK0BF = mkAluK0B.
Proof. fe. unfold mkAluK0BF, mkAluK0B. rewrite mkSrlBF_eq, mkOrBF_eq, mkAndBF_eq, mkAndKBF_eq, mkAluL_fe, zmod64_fe, BASFK.expr_eqbF_fe. reflexivity. Qed.
Lemma foldKBF_fe : BASFK.foldKBG = foldKB.
Proof. fe. apply BASFK.foldKBG_eq. Qed.
Lemma mkAluKBF_eq : mkAluKBF = mkAluKB.
Proof. fe. unfold mkAluKBF, mkAluKB. rewrite mkAluK0BF_eq, foldKBF_fe. reflexivity. Qed.
Lemma mkMdKBF_eq : mkMdKBF = mkMdKB.
Proof. fe. unfold mkMdKBF, mkMdKB. rewrite mkAluKBF_eq. reflexivity. Qed.
Lemma amo_newvalBF_eq : amo_newvalBF = amo_newvalB.
Proof. fe. unfold amo_newvalBF, amo_newvalB. rewrite mkAluKBF_eq. reflexivity. Qed.
Lemma in_sides_disj_sides : forall bc kn b1 k1 n1 b2 k2 n2,
  in_sidesB bc (disj_sidesB bc kn b1 k1 n1) b2 k2 n2 = kdisj_apartB bc kn b1 k1 n1 b2 k2 n2.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [a w v|a l|a l k|lo hi|e m|e lo hi|a n|c1 m1 c2 m2|a l c|a l]; cbn [disj_sidesB kdisj_apartB]; try exact IH.
  destruct (sub_itvB bc b1 k1 n1 c1 m1) eqn:E1; destruct (sub_itvB bc b1 k1 n1 c2 m2) eqn:E2;
    cbn [in_sidesB]; rewrite ?IH; destruct (sub_itvB bc b2 k2 n2 c2 m2), (sub_itvB bc b2 k2 n2 c1 m1); reflexivity.
Qed.

Lemma kdisj_apartB_filter : forall bc kn, kdisj_apartB bc (List.filter is_kdisjb kn) = kdisj_apartB bc kn.
Proof.
  intros bc kn. induction kn as [|K rest IH]; [reflexivity|]. fe.
  destruct K; cbn [List.filter is_kdisjb kdisj_apartB]; rewrite IH; reflexivity.
Qed.
Lemma wr_coveredB_filter : forall bc kn, wr_coveredB bc (List.filter is_kwrb kn) = wr_coveredB bc kn.
Proof.
  intros bc kn. induction kn as [|K rest IH]; [reflexivity|]. fe.
  destruct K as [[]| | | | | |[]| | |]; cbn [List.filter is_kwrb wr_coveredB]; rewrite ?IH; reflexivity.
Qed.
Lemma ranges_apartBF_eq : forall bc b1 k1 n1 b2 k2 n2,
  ranges_apartBF bc (be_kd (mk_bext bc)) (base_rangeB bc b1) b1 k1 n1 b2 k2 n2 = ranges_apartB bc b1 k1 n1 b2 k2 n2.
Proof. intros. unfold ranges_apartBF, ranges_apartB. cbn [be_kd mk_bext]. rewrite kdisj_apartB_filter, BASFK.expr_eqbF_eq. reflexivity. Qed.
Lemma log_lookupBF_eq : forall bc log rb rk n sx hints acc obr,
  (obr = None \/ obr = Some (base_rangeB bc rb)) ->
  log_lookupBF bc (be_kd (mk_bext bc)) obr log rb rk n sx hints acc = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc log rb rk n sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc obr Hobr; [reflexivity|].
  cbn [log_lookupBF log_lookupB].
  assert (Hbr : match obr with Some r => r | None => base_rangeB bc rb end = base_rangeB bc rb)
    by (destruct Hobr as [->| ->]; reflexivity).
  rewrite rel_litF_eq.
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity.
  - apply IH. exact Hobr.
  - rewrite Hbr, ranges_apartBF_eq. destruct (ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)).
    + apply IH. right. reflexivity.
    + destruct hints as [|[|] hs]; try reflexivity; apply IH; right; reflexivity.
Qed.
Lemma wr_numB_covered : forall bc kn a n, wr_numB bc kn a n = true -> wr_coveredB bc kn a n = true.
Proof.
  intros bc kn a n. induction kn as [|K rest IH]; cbn [wr_numB wr_coveredB]; [discriminate|].
  destruct K as [[]| | | | | |[kb kk] len| | |]; try exact IH.
  rewrite BASFK.expr_eqbF_eq. destruct (expr_eqb (a_base a) kb); cbn [andb]; [|intros H; rewrite IH by exact H; destruct (xinsideB _ _ _ _ _ _ _); reflexivity].
  destruct (Z.leb kk (a_off a)); [|intros H; rewrite IH by exact H; destruct (xinsideB _ _ _ _ _ _ _); reflexivity].
  destruct (xloB bc len) as [l|]; [|intros H; rewrite IH by exact H; destruct (xinsideB _ _ _ _ _ _ _); reflexivity].
  destruct (Z.leb (a_off a + Z.of_nat n) (kk + l)); [reflexivity|].
  intros H. rewrite IH by exact H. destruct (xinsideB _ _ _ _ _ _ _); reflexivity.
Qed.
Lemma wr_coveredB_br_eq : forall bc kn a n, wr_coveredB_br bc (base_rangeB bc (a_base a)) kn a n = wr_coveredB bc kn a n.
Proof. intros bc kn a n. induction kn as [|K rest IH]; [reflexivity|]. destruct K as [| | | | | |[kb kk] len| | |]; cbn [wr_coveredB_br wr_coveredB]; rewrite ?IH; reflexivity. Qed.
Lemma storeok_scBF_eq : forall bc, storeok_scBF bc (mk_bext bc) = storeok_scB bc.
Proof.
  intros. fe. unfold storeok_scBF, storeok_scB. rewrite wr_coveredB_br_eq. cbn [be_kw mk_bext].
  destruct (wr_numB bc (List.filter is_kwrb (bc_fk bc)) x x0) eqn:E.
  - apply wr_numB_covered in E. rewrite wr_coveredB_filter in E. rewrite E. reflexivity.
  - rewrite wr_coveredB_filter. reflexivity.
Qed.
Lemma kdisj_apartB_sym : forall bc kn b1 k1 n1 b2 k2 n2, kdisj_apartB bc kn b1 k1 n1 b2 k2 n2 = kdisj_apartB bc kn b2 k2 n2 b1 k1 n1.
Proof.
  intros bc kn b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; [reflexivity|].
  destruct K as [a w v|a l|a l k|lo hi|e m|e lo hi|a n|c1 m1 c2 m2|a l c|a l]; cbn [kdisj_apartB]; try exact IH.
  rewrite IH. destruct (sub_itvB bc b1 k1 n1 c1 m1), (sub_itvB bc b2 k2 n2 c2 m2), (sub_itvB bc b1 k1 n1 c2 m2), (sub_itvB bc b2 k2 n2 c1 m1);
    reflexivity.
Qed.
Lemma ranges_apartBF2_eq : forall bc kb kk w v b1 k1 n1,
  ranges_apartBF2 bc (be_kd (mk_bext bc)) (mk_sctx bc (mk_bext bc) (SE (SA kb kk) w v)) (base_rangeB bc b1) b1 k1 n1 kb kk (Z.of_nat w)
  = ranges_apartB bc b1 k1 n1 kb kk (Z.of_nat w).
Proof.
  intros. unfold ranges_apartBF2, ranges_apartB. rewrite mk_sctx_rng, mk_sctx_D, BASFK.expr_eqbF_eq. cbn [a_base a_off].
  destruct (expr_eqb kb b1); [reflexivity|].
  destruct (Z.eqb (zlit64 (Z.of_nat w)) (Z.of_nat w)) eqn:E.
  - apply Z.eqb_eq in E. rewrite E, in_sides_disj_sides, kdisj_apartB_sym. reflexivity.
  - cbn [be_kd mk_bext]. rewrite kdisj_apartB_filter. reflexivity.
Qed.
Lemma log_lookupBF2_eq : forall bc log rb rk n sx hints acc obr,
  (obr = None \/ obr = Some (base_rangeB bc rb)) ->
  log_lookupBF2 bc (be_kd (mk_bext bc)) obr log (map (mk_sctx bc (mk_bext bc)) log) rb rk n sx hints acc
  = log_lookupB bc log rb rk n sx hints acc.
Proof.
  intros bc log rb rk n sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc obr Hobr; [reflexivity|].
  cbn [map log_lookupBF2 log_lookupB].
  assert (Hbr : match obr with Some r => r | None => base_rangeB bc rb end = base_rangeB bc rb)
    by (destruct Hobr as [->| ->]; reflexivity).
  rewrite rel_litF_eq.
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity.
  - apply IH. exact Hobr.
  - rewrite Hbr, ranges_apartBF2_eq. destruct (ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)).
    + apply IH. right. reflexivity.
    + destruct hints as [|[|] hs]; try reflexivity; apply IH; right; reflexivity.
Qed.
Lemma sym_readBIF_eq : forall segs ss bc kx, KXOK kx ->
  sym_readBIF segs ss bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) = sym_readBI segs ss bc kx.
Proof.
  intros segs ss bc kx HK. fe. unfold sym_readBIF, sym_readBI. rewrite log_lookupBF2_eq by (left; reflexivity).
  rewrite (know_lookupABIF_eq bc kx segs _ _ HK). reflexivity.
Qed.
Local Open Scope Z_scope.
Lemma bv_signedF_G : forall n (b : bv n), bv_signedF b = bv_signedG b.
Proof.
  intros n b. unfold bv_signedF.
  destruct (N.eqb_spec n 12) as [->|_]; [reflexivity|]. destruct (N.eqb_spec n 13) as [->|_]; [reflexivity|].
  destruct (N.eqb_spec n 21) as [->|_]; [reflexivity|]. destruct (N.eqb_spec n 20) as [->|_]; reflexivity.
Qed.
Lemma bv_signedF_eq : forall n (b : bv n), (0 < n)%N -> bv_signedF b = bv_signed b.
Proof.
  intros n b Hn. rewrite bv_signedF_G. unfold bv_signedG, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  pose proof (bv_unsigned_in_range n b) as HR. unfold bv_modulus in HR.
  set (u := bv_unsigned b) in *. set (k := Z.of_N n) in *.
  assert (Hk : 1 <= k) by (unfold k; lia).
  assert (E1 : Z.shiftl 1 (k - 1) = 2 ^ (k - 1)) by (rewrite Z.shiftl_1_l; reflexivity).
  assert (E2 : 2 ^ k = 2 * 2 ^ (k - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (E3 : 2 ^ k / 2 = 2 ^ (k - 1)) by (rewrite E2, Z.mul_comm, Z.div_mul by lia; reflexivity).
  assert (E4 : Z.shiftl (2 ^ (k - 1)) 1 = 2 ^ k) by (rewrite Z.shiftl_mul_pow2 by lia; rewrite E2; lia).
  rewrite E1, E3, E4. pose proof (Z.pow_pos_nonneg 2 (k - 1) ltac:(lia) ltac:(lia)) as HP.
  destruct (Z.ltb_spec u (2 ^ (k - 1))) as [H|H].
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add (u + 2 ^ (k - 1)) (-1) (2 ^ k)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma bv_signedF_fe : forall n, (0 < n)%N -> @bv_signedF n = @bv_signed n.
Proof. intros n Hn. fe. apply bv_signedF_eq. exact Hn. Qed.
Local Close Scope Z_scope.
Local Open Scope Z_scope.
Lemma zsigned64_swrap : forall u, 0 <= u < 2 ^ 64 -> zsigned64 u = bv_swrap 64 u.
Proof.
  intros u Hu. unfold zsigned64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. unfold two63z, two64.
  change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 `div` 2) with (2 ^ 63).
  destruct (Z.leb_spec (2 ^ 63) u) as [H|H].
  - rewrite <- (Z.mod_add (u + 2 ^ 63) (-1) (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.
Lemma lit_branchF_eq : forall c x y, lit_branchF c x y = lit_branch c x y.
Proof.
  intros c x y. unfold lit_branchF, lit_branch, branch_taken, bv_eqb, bv_ltu, bv_lts, bv_signed. cbv zeta.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap at 1 2 3 4 5 6 7 8 9 10 11 12. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite !zmod64_eq.
  pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)) as Bx. pose proof (Z.mod_pos_bound y (2 ^ 64) ltac:(lia)) as By.
  rewrite !zsigned64_swrap by assumption. destruct c; reflexivity.
Qed.
Local Close Scope Z_scope.
Lemma decide_branchBF_eq : decide_branchBF = decide_branchB.
Proof.
  fe. unfold decide_branchBF, decide_branchB. rewrite BASFK.erangeBF_fe, BASFK.expr_eqbF_fe. destruct x1; try reflexivity. destruct x2; try reflexivity. rewrite lit_branchF_eq. reflexivity.
Qed.
Lemma decide_branchBF_h_eq : forall bc cache c a b, BASFK.BCOK bc cache -> decide_branchBF_h bc cache c a b = decide_branchBF bc c a b.
Proof.
  intros bc cache c a b HC. unfold decide_branchBF_h, decide_branchBF. rewrite !(BASFK.erange_h_eq bc cache _ HC), BASFK.erangeBF_fe. reflexivity.
Qed.
Lemma zsx32F_eq : forall v, zsx32F v = zsx32 v.
Proof.
  intros v. unfold zsx32F, zsx32, bv_swrap, bv_wrap. rewrite zmod64_eq2, modp2_eq. reflexivity.
Qed.
Lemma zband32BF_fe : zband32BF = zband32B.
Proof. fe. unfold zband32BF, zband32B. rewrite BASFK.erangeBF_fe. reflexivity. Qed.
Lemma mkAluwKBF_eq : mkAluwKBF = mkAluwKB.
Proof.
  fe. unfold mkAluwKBF, mkAluwKB, mkAluwK0BF, mkAluwK0B. rewrite foldKBF_fe, zband32BF_fe, BASFK.erangeBF_fe. destruct x0; try reflexivity;
    (destruct (is_lit (mkAlu _ x1 x2)); [rewrite zsx32F_eq|]; reflexivity).
Qed.
Lemma conc_exprBF_fe : conc_exprBF = conc_exprB.
Proof. fe. unfold conc_exprBF, conc_exprB. rewrite BASFK.concretizeBG_eq. reflexivity. Qed.
Lemma enum_branchBF_fe : enum_branchBF = enum_branchB.
Proof. fe. unfold enum_branchBF, enum_branchB. destruct (cond_probe x0 x1 x2). rewrite BASFK.concretizeBG_eq. reflexivity. Qed.
Lemma p2n5_eq : forall p, p2n5 p = Pos.to_nat p.
Proof. intros p. do 5 (try destruct p as [p|p|]); reflexivity. Qed.
Lemma ridxF_fe : ridxF = ridx.
Proof. fe. unfold ridxF, ridx. destruct (bv_unsigned x) as [|p|p]; try reflexivity. rewrite p2n5_eq. reflexivity. Qed.
Lemma sr_getF_fe : sr_getF = sr_get.
Proof. fe. unfold sr_getF, sr_get. rewrite ridxF_fe. reflexivity. Qed.
Lemma ssetF_fe : ssetF = sset.
Proof. fe. unfold ssetF, sset. rewrite ridxF_fe. reflexivity. Qed.
Lemma sym_stepBIF_eq : forall bc kx segs i ss scr, KXOK kx ->
  sym_stepBIF bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) segs i ss scr = sym_stepBI bc kx segs i ss scr.
Proof.
  intros bc kx segs i ss scr HK. unfold sym_stepBIF, sym_stepBI. rewrite sr_getF_fe, ssetF_fe, ridxF_fe, mkAluwKBF_eq, conc_exprBF_fe, enum_branchBF_fe. rewrite !(sym_readBIF_eq segs ss bc kx HK), storeok_scBF_eq, zmod64_fe, mkAluKBF_eq, mkMdKBF_eq, amo_newvalBF_eq, decide_branchBF_eq.
  rewrite (bv_signedF_fe 12 ltac:(lia)), (bv_signedF_fe 13 ltac:(lia)), (bv_signedF_fe 20 ltac:(lia)), (bv_signedF_fe 21 ltac:(lia)).
  reflexivity.
Qed.
Local Open Scope Z_scope.
Definition RAOK (br1 : option (Z * Z)) (rk n : Z) (ra : option (PrimInt63.int * PrimInt63.int)) : Prop :=
  match ra with
  | None => True
  | Some (x, y) => match br1 with
                   | Some (lo1, hi1) => Uint63.to_Z x = lo1 + rk + 2 ^ 61 /\ Uint63.to_Z y = hi1 + rk + n + 2 ^ 61
                   | None => False
                   end
  end.
Lemma rann_ok : forall br1 rk n, RAOK br1 rk n (rann br1 rk n).
Proof.
  intros [[lo1 hi1]|] rk n; cbn [rann RAOK]; [|exact I].
  destruct (zb (lo1 + rk)) as [x|] eqn:E1; [|exact I]. destruct (zb (hi1 + rk + n)) as [y|] eqn:E2; [|exact I].
  destruct (zb_spec _ _ E1) as [A1 _]. destruct (zb_spec _ _ E2) as [A2 _]. split; assumption.
Qed.
Lemma rann63_ok : forall e63 br1 rk n, (e63 = None \/ e63 = BASFK.rng63 br1) -> RAOK br1 rk n (rann63 e63 br1 rk n).
Proof.
  intros e63 br1 rk n [->| ->]; [apply rann_ok|]. unfold rann63, BASFK.rng63.
  destruct br1 as [[lo1 hi1]|]; [|apply rann_ok].
  destruct (BASFK.zb lo1) as [lo63|] eqn:E1; [|apply rann_ok]. destruct (BASFK.zb hi1) as [hi63|] eqn:E2; [|apply rann_ok].
  destruct (zb rk) as [k63|] eqn:E3; [|apply rann_ok]. destruct (IMGFK.z61 n) as [n63|] eqn:E4; [|apply rann_ok].
  destruct (BASFK.zb_spec _ _ E1) as [A1 B1]. destruct (BASFK.zb_spec _ _ E2) as [A2 B2]. destruct (zb_spec _ _ E3) as [A3 B3].
  destruct (IMGFK.z61_spec _ _ E4) as [A4 B4].
  assert (EB : Uint63.to_Z EXIK.B61 = 2 ^ 61) by reflexivity.
  cbn [RAOK]. rewrite !Uint63.sub_spec, !Uint63.add_spec, !Uint63.sub_spec, !Uint63.add_spec, EB, A1, A2, A3, A4, wB63.
  rewrite (Z.mod_small (lo1 + 2 ^ 61 + (rk + 2 ^ 61))) by lia. rewrite (Z.mod_small (hi1 + 2 ^ 61 + (rk + 2 ^ 61))) by lia.
  rewrite (Z.mod_small (lo1 + 2 ^ 61 + (rk + 2 ^ 61) - 2 ^ 61)) by lia. rewrite (Z.mod_small (hi1 + 2 ^ 61 + (rk + 2 ^ 61) - 2 ^ 61)) by lia.
  rewrite Z.mod_small by lia. split; lia.
Qed.
Lemma i63apart_sound : forall br1 rk n ra sp kb kk w v, RAOK br1 rk n ra ->
  i63apart ra (sa_rng (sann_sp sp (SE (SA kb kk) w v))) = true ->
  (match br1, sp_rng sp with
   | Some (lo1, hi1), Some (lo2, hi2) => if Z.leb (hi1 + rk + n) (lo2 + kk) then true else Z.leb (hi2 + kk + Z.of_nat w) (lo1 + rk)
   | _, _ => false
   end) = true.
Proof.
  intros br1 rk n ra sp kb kk w v HR H. unfold i63apart, sann_sp in H. cbv zeta in H. cbn [sa_rng e_addr e_width a_off] in H.
  destruct ra as [[rlo rhi]|]; [|discriminate]. cbn [RAOK] in HR.
  destruct br1 as [[lo1 hi1]|]; [|contradiction]. destruct HR as [A1 A2].
  destruct (sp_rng sp) as [[lo2 hi2]|]; [|discriminate].
  destruct (zb (lo2 + kk)) as [slo|] eqn:E3; [|discriminate]. destruct (zb (hi2 + kk + Z.of_nat w)) as [shi|] eqn:E4; [|discriminate].
  destruct (zb_spec _ _ E3) as [A3 _]. destruct (zb_spec _ _ E4) as [A4 _].
  rewrite !IMGFK.leb_b, A1, A2, A3, A4 in H.
  destruct (Z.leb_spec (hi1 + rk + n) (lo2 + kk)) as [L|L]; [reflexivity|].
  destruct (Z.leb_spec (hi1 + rk + n + 2 ^ 61) (lo2 + kk + 2 ^ 61)) as [C|_]; [lia|].
  destruct (Z.leb_spec (hi2 + kk + Z.of_nat w + 2 ^ 61) (lo1 + rk + 2 ^ 61)) as [C|_]; [|discriminate].
  apply Z.leb_le. lia.
Qed.
Lemma flat_scBFa_eq : forall ra br a n, RAOK br (a_off a) (Z.of_nat n) ra -> flat_scBFa ra br a n = flat_scBFr br a n.
Proof.
  intros [[x y]|] br a n H; [|reflexivity]. cbn [RAOK] in H. destruct br as [[lo hi]|]; [|contradiction]. destruct H as [H1 H2].
  unfold flat_scBFa, flat_scBFr. rewrite IMGFK.leb_b, H1. change (Uint63.to_Z EXIK.B61) with (2 ^ 61).
  pose proof (Uint63.to_Z_bounded y) as By. rewrite wB63 in By.
  assert (E2 : Z.leb (hi + a_off a + Z.of_nat n) two64 = true) by (apply Z.leb_le; unfold two64; lia). rewrite E2.
  destruct (Z.leb_spec (2 ^ 61) (lo + a_off a + 2 ^ 61)); destruct (Z.leb_spec 0 (lo + a_off a)); try reflexivity; lia.
Qed.
Local Close Scope Z_scope.
Lemma log_lookupBF3_eq : forall bc kd br1 ra (f : sentry -> sprep) log rb rk n sx hints acc,
  RAOK br1 rk (Z.of_nat n) ra ->
  log_lookupBF3 bc kd br1 ra log (map f log) (map (fun e => sann_sp (f e) e) log) rb rk n (Z.of_nat n) sx hints acc
  = log_lookupBF2 bc kd (Some br1) log (map f log) rb rk n sx hints acc.
Proof.
  intros bc kd br1 ra f log rb rk n sx hints acc Hra. revert hints acc.
  induction log as [|[[kb kk] w v] rest IH]; intros hints acc; [reflexivity|].
  cbn [map log_lookupBF3 log_lookupBF2]. change (sa_zw (sann_sp (f (SE (SA kb kk) w v)) (SE (SA kb kk) w v))) with (Z.of_nat w).
  destruct (rel_litF rb rk (Z.of_nat n) kb kk (Z.of_nat w)) eqn:ER; try reflexivity; [apply IH|].
  assert (NE : BASFK.expr_eqbF kb rb = false).
  { destruct (BASFK.expr_eqbF kb rb) eqn:E; [exfalso|reflexivity]. apply BASFK.expr_eqbF_true in E. subst kb.
    unfold rel_litF in ER. rewrite BASFK.expr_eqbF_refl in ER.
    destruct (if Z.leb kk rk then Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w) else false); [discriminate|].
    destruct (if Z.leb (rk + Z.of_nat n) kk then true else Z.leb (kk + Z.of_nat w) rk); discriminate. }
  assert (HA : i63apart ra (sa_rng (sann_sp (f (SE (SA kb kk) w v)) (SE (SA kb kk) w v))) = true ->
               ranges_apartBF2 bc kd (f (SE (SA kb kk) w v)) br1 rb rk (Z.of_nat n) kb kk (Z.of_nat w) = true).
  { intros HT. apply (i63apart_sound _ _ _ _ _ _ _ _ _ Hra) in HT. unfold ranges_apartBF2. rewrite NE, HT. reflexivity. }
  destruct (i63apart ra (sa_rng (sann_sp (f (SE (SA kb kk) w v)) (SE (SA kb kk) w v)))).
  - rewrite (HA eq_refl). apply IH.
  - destruct (ranges_apartBF2 bc kd (f (SE (SA kb kk) w v)) br1 rb rk (Z.of_nat n) kb kk (Z.of_nat w)); [apply IH|].
    destruct hints as [|[|] hs]; try reflexivity; apply IH.
Qed.

Lemma i63apart_hull : forall ra h r, i63apart ra (hull_join h r) = true -> i63apart ra h = true /\ i63apart ra r = true.
Proof.
  intros [[rlo rhi]|] [[a b]|] [[c d]|] H; cbn [i63apart hull_join] in *; try discriminate.
  rewrite !IMGFK.leb_b in *. rewrite !IMGFK.ltb_b in H.
  destruct (Z.ltb_spec (Uint63.to_Z c) (Uint63.to_Z a)); destruct (Z.ltb_spec (Uint63.to_Z b) (Uint63.to_Z d));
    destruct (Z.leb_spec (Uint63.to_Z rhi) (Uint63.to_Z a)); destruct (Z.leb_spec (Uint63.to_Z rhi) (Uint63.to_Z c));
    destruct (Z.leb_spec (Uint63.to_Z b) (Uint63.to_Z rlo)); destruct (Z.leb_spec (Uint63.to_Z d) (Uint63.to_Z rlo));
    try (split; reflexivity); exfalso;
    repeat match type of H with
           | (if ?x then _ else _) = _ => destruct x eqn:?
           end; try discriminate;
    repeat match goal with
           | E : Z.leb _ _ = true |- _ => apply Z.leb_le in E
           | E : Z.leb _ _ = false |- _ => apply Z.leb_gt in E
           end; lia.
Qed.
Lemma gl_find_add : forall gl kb en rng rb,
  gl_find (gl_add gl kb en rng) rb = if BASFK.expr_eqbF rb kb then en :: gl_find gl rb else gl_find gl rb.
Proof.
  induction gl as [|g r IH]; intros kb en rng rb; cbn [gl_add gl_find lg_b lg_es]; [destruct (BASFK.expr_eqbF rb kb); reflexivity|].
  destruct (BASFK.expr_eqbF kb (lg_b g)) eqn:E; cbn [gl_find lg_b lg_es].
  - apply BASFK.expr_eqbF_true in E. subst kb. destruct (BASFK.expr_eqbF rb (lg_b g)); reflexivity.
  - rewrite IH. destruct (BASFK.expr_eqbF rb (lg_b g)) eqn:E1; [|reflexivity].
    destruct (BASFK.expr_eqbF rb kb) eqn:E2; [|reflexivity].
    apply BASFK.expr_eqbF_true in E1, E2. subst. rewrite BASFK.expr_eqbF_refl in E. discriminate.
Qed.
Lemma gl_others_add : forall gl kb en rng rb ra,
  gl_others_apart (gl_add gl kb en rng) rb ra = true ->
  gl_others_apart gl rb ra = true /\ (BASFK.expr_eqbF rb kb = false -> i63apart ra rng = true).
Proof.
  induction gl as [|g r IH]; intros kb en rng rb ra H; cbn [gl_add gl_others_apart lg_b lg_hull] in *.
  - split; [reflexivity|]. intros E. rewrite E in H. destruct (i63apart ra rng); [reflexivity|discriminate].
  - destruct (BASFK.expr_eqbF kb (lg_b g)) eqn:E; cbn [gl_others_apart lg_b lg_hull] in H.
    + apply BASFK.expr_eqbF_true in E. subst kb. destruct (BASFK.expr_eqbF rb (lg_b g)) eqn:E1.
      * split; [exact H|]. intros C. discriminate.
      * destruct (i63apart ra (hull_join (lg_hull g) rng)) eqn:HA; [|discriminate].
        apply i63apart_hull in HA. destruct HA as [HA1 HA2]. rewrite HA1. split; [exact H|]. intros _. exact HA2.
    + destruct (BASFK.expr_eqbF rb (lg_b g)) eqn:E1.
      * apply IH in H. exact H.
      * destruct (i63apart ra (lg_hull g)); [|discriminate]. apply IH in H. exact H.
Qed.
Lemma eqbF_symf : forall a b, BASFK.expr_eqbF a b = false -> BASFK.expr_eqbF b a = false.
Proof.
  intros a b H. destruct (BASFK.expr_eqbF b a) eqn:E; [|reflexivity]. apply BASFK.expr_eqbF_true in E. subst b.
  rewrite BASFK.expr_eqbF_refl in H. discriminate.
Qed.
Lemma le_scan_sound : forall bc kd br1 ra (f : sentry -> sprep) log rb rk n sx hints r,
  RAOK br1 rk (Z.of_nat n) ra ->
  gl_others_apart (GLof f log) rb ra = true ->
  le_scan (gl_find (GLof f log) rb) rk (Z.of_nat n) n sx hints = Some r ->
  log_lookupBF2 bc kd (Some br1) log (map f log) rb rk n sx hints [] = r.
Proof.
  intros bc kd br1 ra f log rb rk n sx hints r Hra. induction log as [|[[kb kk] w v] rest IH]; intros GA LS.
  - cbn in LS. injection LS as <-. reflexivity.
  - cbn [GLof] in GA, LS. unfold gl_adde in GA, LS. cbn [e_addr e_width e_val a_base a_off] in GA, LS.
    apply gl_others_add in GA. destruct GA as [GA1 GA2]. rewrite gl_find_add in LS.
    change (sa_zw (sann_sp (f (SE (SA kb kk) w v)) (SE (SA kb kk) w v))) with (Z.of_nat w) in LS.
    cbn [map log_lookupBF2]. unfold rel_litF. destruct (BASFK.expr_eqbF rb kb) eqn:E.
    + cbn [le_scan] in LS.
      destruct (if Z.leb kk rk then Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w) else false); [injection LS as <-; reflexivity|].
      destruct (if Z.leb (rk + Z.of_nat n) kk then true else Z.leb (kk + Z.of_nat w) rk); [|discriminate].
      apply IH; assumption.
    + assert (HT : ranges_apartBF2 bc kd (f (SE (SA kb kk) w v)) br1 rb rk (Z.of_nat n) kb kk (Z.of_nat w) = true).
      { specialize (GA2 eq_refl). apply (i63apart_sound _ _ _ _ _ _ _ _ _ Hra) in GA2.
        unfold ranges_apartBF2. rewrite (eqbF_symf _ _ E), GA2. reflexivity. }
      rewrite HT. apply IH; assumption.
Qed.

Definition GOK (g : lgroup) : Prop := forall e, In e (lg_es g) -> (le_zw e <= lg_wmax g)%Z /\ In e (ibucket (lg_idx g) (le_k e)) /\ le_iv e = ivof (le_k e) (le_zw e).
Lemma idx_add_in : forall idx en e, e = en \/ In e (ibucket idx (le_k e)) -> In e (ibucket (idx_add idx en) (le_k e)).
Proof.
  intros idx en e H. unfold idx_add, ibucket at 1.
  destruct (Pos.eq_dec (kx_gkey (le_k e)) (kx_gkey (le_k en))) as [EK|NK].
  - rewrite EK, pt_gss. destruct H as [->|H]; [left; reflexivity|]. right. unfold ibucket in *. rewrite <- EK. exact H.
  - rewrite pt_gso by exact NK. destruct H as [->|H]; [contradiction|exact H].
Qed.
Lemma gl_add_ok : forall gl kb en rng, le_iv en = ivof (le_k en) (le_zw en) -> (forall g, In g gl -> GOK g) -> forall g, In g (gl_add gl kb en rng) -> GOK g.
Proof.
  induction gl as [|g0 r IH]; intros kb en rng HI H g Hg; cbn [gl_add] in Hg.
  - destruct Hg as [<-|[]]. intros e He. cbn [lg_es lg_wmax lg_idx] in *. destruct He as [<-|[]].
    split; [apply Z.le_refl|]. split; [|exact HI]. apply idx_add_in. left. reflexivity.
  - destruct (BASFK.expr_eqbF kb (lg_b g0)).
    + destruct Hg as [<-|Hg]; [|apply H; right; exact Hg].
      intros e He. cbn [lg_es lg_wmax lg_idx] in *. destruct He as [<-|He].
      * split; [apply Z.le_max_r|]. split; [|exact HI]. apply idx_add_in. left. reflexivity.
      * destruct (H g0 (or_introl eq_refl) e He) as [A [B C]]. split; [etransitivity; [exact A|apply Z.le_max_l]|]. split; [|exact C]. apply idx_add_in. right. exact B.
    + destruct Hg as [<-|Hg]; [apply H; left; reflexivity|]. apply (IH kb en rng HI); [|exact Hg]. intros g1 H1. apply H. right. exact H1.
Qed.
Lemma GLof_ok : forall f log g, In g (GLof f log) -> GOK g.
Proof.
  intros f log. induction log as [|e rest IH]; intros g Hg; [destruct Hg|]. cbn [GLof] in Hg. unfold gl_adde in Hg.
  refine (gl_add_ok _ _ _ _ _ IH g Hg). reflexivity.
Qed.
Lemma gl_findg_spec : forall gl rb, match gl_findg gl rb with Some g => In g gl /\ lg_es g = gl_find gl rb | None => gl_find gl rb = [] end.
Proof.
  induction gl as [|g r IH]; intros rb; cbn [gl_findg gl_find]; [reflexivity|].
  destruct (BASFK.expr_eqbF rb (lg_b g)); [split; [left; reflexivity|reflexivity]|].
  specialize (IH rb). destruct (gl_findg r rb); [destruct IH as [A B]; split; [right; exact A|exact B]|exact IH].
Qed.
Lemma bucket_clear_spec : forall l rk zn, bucket_clear l rk zn = true -> forall e, In e l -> le_disj e rk zn = true.
Proof.
  induction l as [|x r IH]; intros rk zn H e He; [destruct He|]. cbn [bucket_clear] in H.
  destruct (le_disj x rk zn) eqn:D; [|discriminate]. destruct He as [<-|He]; [exact D|apply (IH _ _ H e He)].
Qed.
Local Open Scope Z_scope.
Lemma win_clear_spec : forall idx cnt k rk zn, win_clear idx k cnt rk zn = true ->
  forall j, k <= j < k + Z.of_nat cnt -> bucket_clear (ibucket idx j) rk zn = true.
Proof.
  intros idx cnt. induction cnt as [|c IH]; intros k rk zn H j Hj; [lia|]. cbn [win_clear] in H.
  destruct (bucket_clear (ibucket idx k) rk zn) eqn:B; [|discriminate].
  destruct (Z.eq_dec j k) as [->|NE]; [exact B|]. apply (IH (k + 1) rk zn H). lia.
Qed.
Lemma grp_miss_sound : forall g rk zn, GOK g -> grp_miss g rk zn = true -> 0 < zn /\ forall e, In e (lg_es g) -> le_disj e rk zn = true.
Proof.
  intros g rk zn HG H. unfold grp_miss in H.
  destruct (Z.ltb_spec 24 (lg_cnt g)); [|discriminate]. destruct (Z.ltb_spec 0 zn) as [Hz|]; [|discriminate].
  destruct (Z.ltb_spec 0 (lg_wmax g)) as [Hw|]; [|discriminate]. destruct (Z.ltb_spec (lg_wmax g) 65); [|discriminate].
  split; [exact Hz|]. intros e He. destruct (HG e He) as [A [B _]].
  destruct (Z_lt_le_dec (le_k e) (rk - lg_wmax g + 1)) as [L|L].
  - unfold le_disj. destruct (Z.leb_spec (rk + zn) (le_k e)); [reflexivity|]. apply Z.leb_le. lia.
  - destruct (Z_lt_le_dec (le_k e) (rk + zn)) as [L2|L2].
    + apply (bucket_clear_spec _ _ _ (win_clear_spec _ _ _ _ _ H (le_k e) ltac:(rewrite Z2Nat.id by lia; lia)) e B).
    + unfold le_disj. destruct (Z.leb_spec (rk + zn) (le_k e)); [reflexivity|lia].
Qed.
Lemma le_scan_alldisj : forall es rk zn n sx hints, 0 < zn -> (forall e, In e es -> le_disj e rk zn = true) ->
  le_scan es rk zn n sx hints = Some (LMiss [] hints).
Proof.
  induction es as [|[kk zw w v iv] r IH]; intros rk zn n sx hints Hz H; [reflexivity|]. cbn [le_scan].
  pose proof (H _ (or_introl eq_refl)) as D. unfold le_disj in D. cbn [le_k le_zw] in D.
  destruct (Z.leb_spec kk rk) as [A|A].
  - destruct (Z.leb_spec (rk + zn) (kk + zw)) as [B|B].
    + exfalso. destruct (Z.leb_spec (rk + zn) kk); [lia|]. apply Z.leb_le in D. lia.
    + rewrite D. apply IH; [exact Hz|]. intros e He. apply H. right. exact He.
  - rewrite D. apply IH; [exact Hz|]. intros e He. apply H. right. exact He.
Qed.
Local Close Scope Z_scope.
Local Open Scope Z_scope.
Lemma ivof_spec : forall k w s e, ivof k w = Some (s, e) ->
  Uint63.to_Z s = k + 2 ^ 61 /\ Uint63.to_Z e = k + w + 2 ^ 61 /\ - 2 ^ 60 < k < 2 ^ 60 /\ 0 <= w < 2 ^ 61.
Proof.
  intros k w s e H. unfold ivof in H. destruct (zb k) as [s0|] eqn:Es; [|discriminate]. destruct (IMGFK.z61 w) as [w63|] eqn:Ew; [|discriminate].
  injection H as <- <-. destruct (zb_spec _ _ Es) as [S1 S2]. destruct (IMGFK.z61_spec _ _ Ew) as [W1 W2].
  rewrite Uint63.add_spec, S1, W1, wB63, Z.mod_small by lia. repeat split; lia.
Qed.
Lemma le_scanI_eq : forall es rk zn n sx hints, (forall e, In e es -> le_iv e = ivof (le_k e) (le_zw e)) ->
  le_scanI es (ivof rk zn) rk zn n sx hints = le_scan es rk zn n sx hints.
Proof.
  induction es as [|[kk zw w v iv] r IH]; intros rk zn n sx hints H; [reflexivity|]. cbn [le_scanI le_scan].
  assert (IH' : le_scanI r (ivof rk zn) rk zn n sx hints = le_scan r rk zn n sx hints) by (apply IH; intros e He; apply H; right; exact He).
  pose proof (H _ (or_introl eq_refl)) as HI. cbn [le_iv le_k le_zw] in HI. subst iv.
  destruct (ivof kk zw) as [[s e]|] eqn:E1; [|rewrite IH'; reflexivity].
  destruct (ivof rk zn) as [[q qe]|] eqn:E2; [|rewrite IH'; reflexivity].
  destruct (ivof_spec _ _ _ _ E1) as (A1 & A2 & A3 & A4). destruct (ivof_spec _ _ _ _ E2) as (B1 & B2 & B3 & B4).
  rewrite !IMGFK.leb_b, A1, A2, B1, B2, IH'.
  replace (Z.leb (kk + 2 ^ 61) (rk + 2 ^ 61)) with (Z.leb kk rk) by (destruct (Z.leb_spec kk rk), (Z.leb_spec (kk + 2 ^ 61) (rk + 2 ^ 61)); try reflexivity; lia).
  replace (Z.leb (rk + zn + 2 ^ 61) (kk + zw + 2 ^ 61)) with (Z.leb (rk + zn) (kk + zw)) by (destruct (Z.leb_spec (rk + zn) (kk + zw)), (Z.leb_spec (rk + zn + 2 ^ 61) (kk + zw + 2 ^ 61)); try reflexivity; lia).
  replace (Z.leb (rk + zn + 2 ^ 61) (kk + 2 ^ 61)) with (Z.leb (rk + zn) kk) by (destruct (Z.leb_spec (rk + zn) kk), (Z.leb_spec (rk + zn + 2 ^ 61) (kk + 2 ^ 61)); try reflexivity; lia).
  replace (Z.leb (kk + zw + 2 ^ 61) (rk + 2 ^ 61)) with (Z.leb (kk + zw) rk) by (destruct (Z.leb_spec (kk + zw) rk), (Z.leb_spec (kk + zw + 2 ^ 61) (rk + 2 ^ 61)); try reflexivity; lia).
  reflexivity.
Qed.
Local Close Scope Z_scope.
Lemma grp_scan_eq : forall gl rb rk zn n sx hints, (forall g, In g gl -> GOK g) ->
  grp_scan gl rb rk zn n sx hints = le_scan (gl_find gl rb) rk zn n sx hints.
Proof.
  intros gl rb rk zn n sx hints HG. unfold grp_scan. pose proof (gl_findg_spec gl rb) as S.
  destruct (gl_findg gl rb) as [g|]; [|rewrite S; reflexivity]. destruct S as [Sin Ses]. rewrite <- Ses.
  destruct (grp_miss g rk zn) eqn:M; [|apply le_scanI_eq; intros e He; apply (HG g Sin e He)].
  destruct (grp_miss_sound g rk zn (HG g Sin) M) as [Hz HD]. symmetry. apply le_scan_alldisj; assumption.
Qed.
Lemma log_lookupG_eq : forall bc kd br1 ra (f : sentry -> sprep) log rb rk n sx hints,
  RAOK br1 rk (Z.of_nat n) ra ->
  log_lookupG bc kd br1 ra (GLof f log) log (map f log) (map (fun e => sann_sp (f e) e) log) rb rk n (Z.of_nat n) sx hints
  = log_lookupBF2 bc kd (Some br1) log (map f log) rb rk n sx hints [].
Proof.
  intros bc kd br1 ra f log rb rk n sx hints Hra. unfold log_lookupG. rewrite (grp_scan_eq _ _ _ _ _ _ _ (GLof_ok f log)).
  destruct (gl_others_apart (GLof f log) rb ra) eqn:GA; [|apply log_lookupBF3_eq; exact Hra].
  destruct (le_scan (gl_find (GLof f log) rb) rk (Z.of_nat n) n sx hints) as [r|] eqn:LS; [|apply log_lookupBF3_eq; exact Hra].
  symmetry. apply (le_scan_sound bc kd br1 ra f log rb rk n sx hints r Hra GA LS).
Qed.
Lemma sym_readBIFr_spec : forall segs ss bc kx c scr e63 a n sx', KXOK kx -> BASFK.BCOK bc c ->
  (e63 = None \/ e63 = BASFK.rng63 (base_rangeB bc (a_base a))) ->
  fst (sym_readBIFr segs ss bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
    (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c scr (base_rangeB bc (a_base a)) e63 a n sx')
  = sym_readBI segs ss bc kx scr a n sx'
  /\ BASFK.BCOK bc (snd (sym_readBIFr segs ss bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
    (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c scr (base_rangeB bc (a_base a)) e63 a n sx')).
Proof.
  intros segs ss bc kx c scr e63 a n sx' HK HC HE. unfold sym_readBIFr, sym_readBI. cbv zeta.
  pose proof (rann63_ok e63 (base_rangeB bc (a_base a)) (a_off a) (Z.of_nat n) HE) as HR.
  rewrite (log_lookupG_eq _ _ _ _ _ _ _ _ _ _ _ HR).
  rewrite log_lookupBF2_eq by (right; reflexivity).
  rewrite (know_lookupABIF_eq bc kx segs _ _ HK). rewrite !(flat_scBFa_eq _ _ _ _ HR).
  destruct (log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) as [v scs hints|scs hints|].
  - destruct (BASFK.foldKB_c_spec bc c (extK0B bc v) HC) as [E O]. destruct (BASFK.foldKB_c bc c (extK0B bc v)) as [v' c'].
    cbn [fst snd] in *. subst v'. split; [reflexivity|exact O].
  - destruct (know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs) as [v scs' hints'|scs' hints'|].
    + destruct (BASFK.foldKB_c_spec bc c (extK0B bc v) HC) as [E O]. destruct (BASFK.foldKB_c bc c (extK0B bc v)) as [v' c'].
      cbn [fst snd] in *. subst v'. split; [reflexivity|exact O].
    + split; [reflexivity|exact HC].
    + split; [reflexivity|exact HC].
  - split; [reflexivity|exact HC].
Qed.
Definition step_c_ok (bc : bctx) (kx : kix) (segs : list Segment) (c : BASFK.bcache) (i : instr) (ss : sym_state) (scr : scripts) : Prop :=
  fst (sym_stepBIF_c bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c segs i ss scr) = sym_stepBI bc kx segs i ss scr
  /\ BASFK.BCOK bc (snd (sym_stepBIF_c bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c segs i ss scr)).
Lemma step_c_default : forall bc kx segs c i ss scr, KXOK kx -> BASFK.BCOK bc c ->
  sym_stepBIF_c bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c segs i ss scr
  = (sym_stepBIF bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) segs i ss scr, c) ->
  step_c_ok bc kx segs c i ss scr.
Proof. intros bc kx segs c i ss scr HK HC E. unfold step_c_ok. rewrite E. cbn [fst snd]. split; [apply sym_stepBIF_eq; exact HK|exact HC]. Qed.
Lemma step_c_opimm : forall bc kx segs c op rd rs imm ss scr, KXOK kx -> BASFK.BCOK bc c -> step_c_ok bc kx segs c (OpImm op rd rs imm) ss scr.
Proof.
  intros bc kx segs c op rd rs imm ss scr HK HC.
  destruct op;
  try (unfold step_c_ok; cbn [sym_stepBIF_c]; cbv zeta; rewrite sr_getF_fe, ssetF_fe;
       match goal with |- context [BASFK.foldKB_c bc c ?x] =>
         destruct (BASFK.foldKB_c_spec bc c x HC) as [E1 O1]; destruct (BASFK.foldKB_c bc c x) as [v c1] end;
       cbn [fst snd] in *; subst v; split; [|exact O1];
       unfold sym_stepBI, mkAluKB; rewrite mkAluK0BF_eq, (bv_signedF_eq 12 imm ltac:(lia)); reflexivity).
  unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ssetF_fe.
  destruct (BASFK.mkAluKB_add_c_spec bc c (sr_get (s_regs ss) rs) (bv_signedF imm) HC) as [E1 O1].
  destruct (BASFK.mkAluKB_add_c bc c (sr_get (s_regs ss) rs) (bv_signedF imm)) as [v c1]. cbn [fst snd] in *. subst v.
  split; [|exact O1]. rewrite (bv_signedF_eq 12 imm ltac:(lia)). reflexivity.
Qed.
Lemma step_c_shimm : forall bc kx segs c op rd rs sh ss scr, KXOK kx -> BASFK.BCOK bc c -> step_c_ok bc kx segs c (ShiftImm op rd rs sh) ss scr.
Proof.
  intros bc kx segs c op rd rs sh ss scr HK HC.
  unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ssetF_fe.
  match goal with |- context [BASFK.foldKB_c bc c ?x] =>
    destruct (BASFK.foldKB_c_spec bc c x HC) as [E1 O1]; destruct (BASFK.foldKB_c bc c x) as [v c1] end.
  cbn [fst snd] in *. subst v. split; [|exact O1]. unfold sym_stepBI, mkAluKB. rewrite mkAluK0BF_eq. reflexivity.
Qed.
Lemma step_c_op : forall bc kx segs c op rd rs1 rs2 ss scr, KXOK kx -> BASFK.BCOK bc c -> step_c_ok bc kx segs c (Op op rd rs1 rs2) ss scr.
Proof.
  intros bc kx segs c op rd rs1 rs2 ss scr HK HC.
  assert (GEN : sym_stepBIF_c bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c segs (Op op rd rs1 rs2) ss scr
      = (let '(v, c1) := BASFK.foldKB_c bc c (mkAluK0BF bc op (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)) in (SOk (ssetF ss rd v (s_pc ss + 4)) [] scr, c1)) ->
      step_c_ok bc kx segs c (Op op rd rs1 rs2) ss scr).
  { intros EQ. unfold step_c_ok. rewrite EQ. rewrite ssetF_fe.
    match goal with |- context [BASFK.foldKB_c bc c ?y] =>
      destruct (BASFK.foldKB_c_spec bc c y HC) as [E1 O1]; destruct (BASFK.foldKB_c bc c y) as [v c1] end.
    cbn [fst snd] in *. subst v. split; [|exact O1]. unfold sym_stepBI, mkAluKB. rewrite mkAluK0BF_eq. reflexivity. }
  destruct op; try (apply GEN; cbn [sym_stepBIF_c]; cbv zeta; rewrite sr_getF_fe; destruct (sr_get (s_regs ss) rs2); reflexivity).
  clear GEN.
  destruct (sr_get (s_regs ss) rs2) as [z| | | | | | |] eqn:E2;
  try (unfold step_c_ok; cbn [sym_stepBIF_c]; cbv zeta; rewrite sr_getF_fe, ssetF_fe, E2;
        match goal with |- context [BASFK.foldKB_c bc c ?y] =>
          destruct (BASFK.foldKB_c_spec bc c y HC) as [E1 O1]; destruct (BASFK.foldKB_c bc c y) as [v c1] end;
        cbn [fst snd] in *; subst v; split; [|exact O1]; unfold sym_stepBI, mkAluKB; rewrite mkAluK0BF_eq, E2; reflexivity).
  unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ssetF_fe, E2.
  destruct (BASFK.mkAluKB_add_c_spec bc c (sr_get (s_regs ss) rs1) z HC) as [E1 O1].
  destruct (BASFK.mkAluKB_add_c bc c (sr_get (s_regs ss) rs1) z) as [v c1]. cbn [fst snd] in *. subst v.
  split; [|exact O1]. unfold sym_stepBI. rewrite E2. reflexivity.
Qed.
Lemma step_c_load : forall bc kx segs c sz sg rd rs imm ss scr, KXOK kx -> BASFK.BCOK bc c -> step_c_ok bc kx segs c (Load sz sg rd rs imm) ss scr.
Proof.
  intros bc kx segs c sz sg rd rs imm ss scr HK HC. unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ridxF_fe.
  destruct (BASFK.to_saddrKB_c_spec bc c (sr_get (s_regs ss) rs) (bv_signedF imm) HC) as [E1 O1].
  destruct (BASFK.to_saddrKB_c bc c (sr_get (s_regs ss) rs) (bv_signedF imm)) as [a c1]. cbn [fst snd] in E1, O1. subst a.
  destruct (BASFK.base_range63_c_spec bc c1 (a_base (to_saddrKB bc (sr_get (s_regs ss) rs) (bv_signedF imm))) O1) as (E2 & E2' & O2).
  destruct (BASFK.base_range63_c bc c1 (a_base (to_saddrKB bc (sr_get (s_regs ss) rs) (bv_signedF imm)))) as [[br e63] c2]. cbn [fst snd] in E2, E2', O2. subst br.
  destruct (sym_readBIFr_spec segs ss bc kx c2 scr e63 (to_saddrKB bc (sr_get (s_regs ss) rs) (bv_signedF imm)) (msize_bytes sz)
              (match sz with SZ8 => false | _ => sg end) HK O2 E2') as [E3 O3].
  destruct (sym_readBIFr segs ss bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
              (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c2 scr
              (base_rangeB bc (a_base (to_saddrKB bc (sr_get (s_regs ss) rs) (bv_signedF imm)))) e63
              (to_saddrKB bc (sr_get (s_regs ss) rs) (bv_signedF imm)) (msize_bytes sz) (match sz with SZ8 => false | _ => sg end)) as [r c3].
  cbn [fst snd] in E3, O3. subst r.
  split; [|exact O3]. cbn [fst]. rewrite (bv_signedF_eq 12 imm ltac:(lia)). reflexivity.
Qed.
Lemma step_c_store : forall bc kx segs c sz rs1 rs2 imm ss scr, KXOK kx -> BASFK.BCOK bc c -> step_c_ok bc kx segs c (Store sz rs1 rs2 imm) ss scr.
Proof.
  intros bc kx segs c sz rs1 rs2 imm ss scr HK HC. unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe.
  destruct (BASFK.to_saddrKB_c_spec bc c (sr_get (s_regs ss) rs1) (bv_signedF imm) HC) as [E1 O1].
  destruct (BASFK.to_saddrKB_c bc c (sr_get (s_regs ss) rs1) (bv_signedF imm)) as [a c1]. cbn [fst snd] in E1, O1. subst a.
  rewrite (bv_signedF_eq 12 imm ltac:(lia)) in *.
  unfold sym_stepBI. destruct (resv_inval (s_resv ss) (to_saddrKB bc (sr_get (s_regs ss) rs1) (bv_signed imm))) as [r'|]; [|split; [reflexivity|exact O1]].
  destruct (BASFK.base_range_c_spec bc c1 (a_base (to_saddrKB bc (sr_get (s_regs ss) rs1) (bv_signed imm))) O1) as [E2 O2].
  destruct (BASFK.base_range_c bc c1 (a_base (to_saddrKB bc (sr_get (s_regs ss) rs1) (bv_signed imm)))) as [br c2]. cbn [fst snd] in E2, O2. subst br.
  split; [|exact O2]. cbn [fst]. rewrite storeok_scBF_eq. reflexivity.
Qed.
Ltac use_addr HC c1 O1 :=
  match goal with
  | |- context [BASFK.to_saddrKB_c ?bc ?c ?e ?imm] =>
      let E1 := fresh "E1" in let a := fresh "a" in
      destruct (BASFK.to_saddrKB_c_spec bc c e imm HC) as [E1 O1];
      destruct (BASFK.to_saddrKB_c bc c e imm) as [a c1]; cbn [fst snd] in E1, O1; subst a
  end.
Ltac use_br O1 c2 O2 :=
  match goal with
  | |- context [BASFK.base_range_c ?bc ?c1 ?B] =>
      let E2 := fresh "E2" in let br := fresh "br" in
      destruct (BASFK.base_range_c_spec bc c1 B O1) as [E2 O2];
      destruct (BASFK.base_range_c bc c1 B) as [br c2]; cbn [fst snd] in E2, O2; subst br
  end.
Ltac use_br63 O1 c2 O2 E2' :=
  match goal with
  | |- context [BASFK.base_range63_c ?bc ?c1 ?B] =>
      let E2 := fresh "E2" in let br := fresh "br" in let e63 := fresh "e63" in
      destruct (BASFK.base_range63_c_spec bc c1 B O1) as (E2 & E2' & O2);
      destruct (BASFK.base_range63_c bc c1 B) as [[br e63] c2]; cbn [fst snd] in E2, E2', O2; subst br
  end.
Ltac use_read HK O2 E2' c3 O3 :=
  match goal with
  | |- context [sym_readBIFr ?segs ?ss ?bc ?kx ?xc ?ex ?lis ?lia ?gl ?c2 ?scr (base_rangeB ?bc (a_base ?a)) ?e63 ?a ?n ?sx] =>
      let E3 := fresh "E3" in let r := fresh "r" in
      destruct (sym_readBIFr_spec segs ss bc kx c2 scr e63 a n sx HK O2 E2') as [E3 O3];
      destruct (sym_readBIFr segs ss bc kx xc ex lis lia gl c2 scr (base_rangeB bc (a_base a)) e63 a n sx) as [r c3]; cbn [fst snd] in E3, O3; subst r
  end.
Lemma step_c_lr : forall bc kx segs c wd aq rl rd rs ss scr, KXOK kx -> BASFK.BCOK bc c -> step_c_ok bc kx segs c (Lr wd aq rl rd rs) ss scr.
Proof.
  intros bc kx segs c wd aq rl rd rs ss scr HK HC. unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ridxF_fe.
  unfold sym_stepBI. destruct (amo_alignedbB bc (sr_get (s_regs ss) rs) wd); [|split; [reflexivity|exact HC]].
  use_addr HC c1 O1. use_br63 O1 c2 O2 E2'. use_read HK O2 E2' c3 O3. split; [reflexivity|exact O3].
Qed.
Lemma step_c_sc : forall bc kx segs c wd aq rl rd rs1 rs2 ss scr, KXOK kx -> BASFK.BCOK bc c -> step_c_ok bc kx segs c (Sc wd aq rl rd rs1 rs2) ss scr.
Proof.
  intros bc kx segs c wd aq rl rd rs1 rs2 ss scr HK HC. unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ridxF_fe.
  unfold sym_stepBI. destruct (amo_alignedbB bc (sr_get (s_regs ss) rs1) wd); [|split; [reflexivity|exact HC]].
  use_addr HC c1 O1. destruct (s_resv ss) as [r|]; [|split; [reflexivity|exact O1]].
  destruct (saddr_eqb r (to_saddrKB bc (sr_get (s_regs ss) rs1) 0)); [|split; [reflexivity|exact O1]].
  use_br O1 c2 O2. split; [|exact O2]. cbn [fst]. rewrite storeok_scBF_eq. reflexivity.
Qed.
Lemma step_c_amo : forall bc kx segs c op wd aq rl rd rs1 rs2 ss scr, KXOK kx -> BASFK.BCOK bc c -> step_c_ok bc kx segs c (Amo op wd aq rl rd rs1 rs2) ss scr.
Proof.
  intros bc kx segs c op wd aq rl rd rs1 rs2 ss scr HK HC. unfold step_c_ok. cbn [sym_stepBIF_c]. cbv zeta. rewrite sr_getF_fe, ridxF_fe.
  unfold sym_stepBI. destruct (amo_aluop op) as [aop|]; [|split; [reflexivity|exact HC]].
  destruct (amo_alignedbB bc (sr_get (s_regs ss) rs1) wd); [|split; [reflexivity|exact HC]].
  use_addr HC c1 O1. destruct (resv_inval (s_resv ss) (to_saddrKB bc (sr_get (s_regs ss) rs1) 0)) as [r'|]; [|split; [reflexivity|exact O1]].
  use_br63 O1 c2 O2 E2'. use_read HK O2 E2' c3 O3. split; [|exact O3]. cbn [fst]. rewrite storeok_scBF_eq, amo_newvalBF_eq. reflexivity.
Qed.
Lemma step_c_branch : forall bc kx segs c cnd rs1 rs2 imm ss scr, KXOK kx -> BASFK.BCOK bc c -> step_c_ok bc kx segs c (Branch cnd rs1 rs2 imm) ss scr.
Proof.
  intros bc kx segs c cnd rs1 rs2 imm ss scr HK HC. apply step_c_default; [exact HK|exact HC|].
  cbn [sym_stepBIF_c sym_stepBIF]. cbv zeta. rewrite (decide_branchBF_h_eq bc c cnd _ _ HC). reflexivity.
Qed.
Lemma sym_stepBIF_c_spec : forall bc kx segs c i ss scr, KXOK kx -> BASFK.BCOK bc c -> step_c_ok bc kx segs c i ss scr.
Proof.
  intros bc kx segs c i ss scr HK HC.
  destruct i; first [apply step_c_opimm; assumption | apply step_c_shimm; assumption | apply step_c_op; assumption | apply step_c_branch; assumption | apply step_c_load; assumption | apply step_c_store; assumption
                    | apply step_c_lr; assumption | apply step_c_sc; assumption | apply step_c_amo; assumption
                    | apply step_c_default; [exact HK|exact HC|reflexivity]].
Qed.
Lemma sym_readBI_next : forall segs ss bc kx scr a n sx v scs scr' nx',
  sym_readBI segs ss bc kx scr a n sx = Some (v, scs, scr', nx') -> Nat.leb (s_next ss) nx' = true.
Proof.
  intros segs ss bc kx scr a n sx v scs scr' nx' H. unfold sym_readBI in H.
  destruct (log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx (sc_hints scr) []) as [v0 scs0 h0|scs0 h0|]; [| |discriminate].
  - injection H as _ _ _ <-. apply Nat.leb_refl.
  - destruct (know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx h0 scs0) as [v1 scs1 h1|scs1 h1|]; [| |discriminate].
    + injection H as _ _ _ <-. apply Nat.leb_refl.
    + injection H as _ _ _ <-. apply Nat.leb_le. apply Nat.le_succ_diag_r.
Qed.
Lemma step_next_mono : forall bc kx segs i ss scr ss' scs scr',
  sym_stepBI bc kx segs i ss scr = SOk ss' scs scr' -> Nat.leb (s_next ss) (s_next ss') = true.
Proof.
  intros bc kx segs i ss scr ss' scs scr' H. unfold sym_stepBI in H.
  destruct i; cbv beta iota zeta in H;
    repeat match type of H with
           | context [sym_readBI ?a ?b ?c ?d ?e ?f ?g ?h] =>
               let ER := fresh "ER" in
               destruct (sym_readBI a b c d e f g h) as [[[[? ?] ?] ?]|] eqn:ER; [apply sym_readBI_next in ER|]
           | context [match ?x with _ => _ end] => destruct x
           end; try discriminate; injection H as <- _ _; cbn [s_next sset sjump]; first [apply Nat.leb_refl | assumption].
Qed.

Lemma existsb_ext' : forall (A : Type) (f g : A -> bool) l, (forall a, f a = g a) -> existsb f l = existsb g l.
Proof. intros A f g l H. induction l as [|a r IH]; [reflexivity|]. cbn [existsb]. rewrite H, IH. reflexivity. Qed.
Lemma existsbL_eq : forall (A : Type) (f : A -> bool) l, existsbL f l = existsb f l.
Proof. intros A f l. induction l as [|a r IH]; [reflexivity|]. cbn [existsbL existsb]. rewrite IH. reflexivity. Qed.
Lemma kentry_overlayBF_eq : forall bc rb rk n K, kentry_overlayBF bc rb rk (Z.of_nat n) K = kentry_overlayB bc rb rk n K.
Proof.
  intros bc rb rk n K. unfold kentry_overlayBF, kentry_overlayB, zf_coversBF, zf_coversB, elen. rewrite ?rel_litF_fe.
  destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity;
    (destruct len; try reflexivity; rewrite zmod64_eq; reflexivity).
Qed.
Lemma kentry_readableBF_eq : forall bc rb rk n K, kentry_readableBF bc rb rk (Z.of_nat n) K = kentry_readableB bc rb rk n K.
Proof.
  intros bc rb rk n K. unfold kentry_readableBF, kentry_readableB. rewrite ?rel_litF_fe.
  destruct K as [[kb kk] w v|a len|a len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|a len c|a len]; try reflexivity; apply kentry_overlayBF_eq.
Qed.
Lemma kn_readableBF_eq : forall segs bc kn rb rk n, bc = mkbc (bc_fk bc) ->
  kn_readableBF segs bc kn rb rk n = kn_readable segs (bc_fk bc) kn rb rk n.
Proof.
  intros segs bc kn rb rk n HB. rewrite <- (kn_readableB_eqf segs (bc_fk bc)), <- HB.
  unfold kn_readableBF, kn_readableB. rewrite existsbL_eq.
  rewrite (existsb_ext' _ (kentry_readableBF bc rb rk (Z.of_nat n)) (kentry_readableB bc rb rk n) kn) by (intros K; apply kentry_readableBF_eq).
  reflexivity.
Qed.
Lemma kn_overlayBF_eq : forall segs bc kn rb rk n, bc = mkbc (bc_fk bc) ->
  kn_overlayBF segs bc kn rb rk n = kn_overlay segs (bc_fk bc) kn rb rk n.
Proof.
  intros segs bc kn rb rk n HB. rewrite <- (kn_overlayB_eqf segs (bc_fk bc)), <- HB.
  unfold kn_overlayBF, kn_overlayB. rewrite existsbL_eq.
  rewrite (existsb_ext' _ (kentry_overlayBF bc rb rk (Z.of_nat n)) (kentry_overlayB bc rb rk n) kn) by (intros K; apply kentry_overlayBF_eq).
  reflexivity.
Qed.
Lemma x_dischargeableBF_eq : forall segs bc ss ss' rb sc, bc = mkbc (bc_fk bc) ->
  x_dischargeableBF segs bc ss ss' rb sc = x_dischargeableB segs bc ss ss' rb sc.
Proof.
  intros segs bc ss ss' rb sc HB. unfold x_dischargeableBF, x_dischargeableB. cbv zeta.
  destruct sc as [t c a b|a n|a1 n1 a2 n2|a1 n1 a2 n2|a n|a n sx e|a b]; try reflexivity.
  - destruct n; try reflexivity. rewrite (kn_readableBF_eq segs bc _ _ _ _ HB).
    destruct (Z.leb 1 z); [|reflexivity]. destruct (Z.leb z 8); reflexivity.
  - rewrite (kn_overlayBF_eq segs bc _ _ _ _ HB). destruct (Nat.leb 1 n); [|reflexivity]. destruct (Nat.leb n 8); reflexivity.
  - destruct e; try reflexivity. rewrite (kn_readableBF_eq segs bc _ _ _ _ HB).
    destruct rb as [[[a' n'] sx']|]; [|reflexivity].
    destruct (saddr_eqb a' a); [|reflexivity]. destruct (Nat.eqb n' n); [|reflexivity]. destruct (Bool.eqb sx' sx); [|reflexivity]. cbn [andb].
    destruct (Nat.eqb n0 (s_next ss)); [|reflexivity]. destruct (Nat.ltb n0 (s_next ss')); [|reflexivity].
    destruct (evars_lt (s_next ss) (a_base a)); [|reflexivity]. destruct (Nat.leb 1 n); [|reflexivity]. destruct (Nat.leb n 8); reflexivity.
Qed.
Lemma x_filterBF_eq : forall segs bc ss ss' scs, bc = mkbc (bc_fk bc) -> x_filterBF segs bc ss ss' scs = x_filterB segs bc ss ss' scs.
Proof.
  intros segs bc ss ss' scs HB. unfold x_filterBF, x_filterB. destruct scs as [|sc rest]; [reflexivity|].
  apply filter_ext. intros x. rewrite (x_dischargeableBF_eq segs bc ss ss' _ x HB). reflexivity.
Qed.
Lemma sym_stepXBIF_spec : forall segs bc kx c K i ss scr, KXOK kx -> bc = mkbc (bc_fk bc) -> BASFK.BCOK bc c ->
  fst (sym_stepXBIF segs bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c K i ss scr) = sym_stepXBI segs bc kx K i ss scr
  /\ BASFK.BCOK bc (snd (sym_stepXBIF segs bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c K i ss scr)).
Proof.
  intros segs bc kx c K i ss scr HK HB HC. unfold sym_stepXBIF, sym_stepXBI.
  destruct (sym_stepBIF_c_spec bc kx segs c i ss scr HK HC) as [E O].
  destruct (sym_stepBIF_c bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c segs i ss scr) as [r c'].
  cbn [fst snd] in *. subst r. split; [|exact O].
  destruct (sym_stepBI bc kx segs i ss scr) as [ss' scs scr'|] eqn:E; [|reflexivity].
  rewrite (step_next_mono _ _ _ _ _ _ _ _ _ E), (x_filterBF_eq segs bc ss ss' scs HB). reflexivity.
Qed.

Lemma step_log : forall bc kx segs i ss scr ss' scs scr',
  sym_stepBI bc kx segs i ss scr = SOk ss' scs scr' ->
  if is_store_instr i then exists e, s_log ss' = e :: s_log ss else s_log ss' = s_log ss.
Proof.
  intros bc kx segs i ss scr ss' scs scr' H. unfold sym_stepBI in H.
  destruct i; cbv beta iota zeta in H; cbn [is_store_instr];
    repeat match type of H with
           | context [match ?x with _ => _ end] => destruct x
           end; try discriminate; injection H as <- _ _; cbn [s_log sset sjump]; eauto.
Qed.
Lemma is_stopF_eq : forall stops pc, is_stopF (mk_stt stops) stops pc = existsb (Z.eqb pc) stops.
Proof.
  intros stops pc. unfold is_stopF. destruct pc as [|p|p]; try reflexivity.
  induction stops as [|z r IH]; [cbn; rewrite pt_get_leaf; reflexivity|].
  cbn [mk_stt existsb]. destruct z as [|q|q]; try exact IH.
  change (Z.eqb (Zpos p) (Zpos q)) with (Pos.eqb p q). destruct (Pos.eqb_spec p q) as [->|NE].
  - rewrite pt_gss. reflexivity.
  - rewrite pt_gso by exact NE. exact IH.
Qed.
Lemma lupd_ok : forall segs bc kx K i ss scr ss' scs scr' wc,
  sym_stepXBI segs bc kx K i ss scr = SOk ss' scs scr' -> WCOK bc (mk_bext bc) wc ->
  exists wc', lupd bc (mk_bext bc) i ss' (map (mk_sctx bc (mk_bext bc)) (s_log ss)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss))
                (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) wc
              = (map (mk_sctx bc (mk_bext bc)) (s_log ss'), map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss'),
                 GLof (mk_sctx bc (mk_bext bc)) (s_log ss'), wc')
              /\ WCOK bc (mk_bext bc) wc'.
Proof.
  intros segs bc kx K i ss scr ss' scs scr' wc H HW. unfold sym_stepXBI in H.
  destruct (sym_stepBI bc kx segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  assert (HL : s_log (cap_rd K i ss1) = s_log ss1).
  { unfold cap_rd. destruct K; [reflexivity|]. destruct (rd_of i) as [rd|]; [|reflexivity].
    destruct (bv_eqb rd 0); [reflexivity|]. destruct (esize_le (sr_get (s_regs ss1) rd) (S K)); reflexivity. }
  pose proof (step_log _ _ _ _ _ _ _ _ _ E) as HS. unfold lupd. rewrite HL.
  destruct (is_store_instr i).
  - destruct HS as [e He]. rewrite He.
    pose proof (mk_sctx_c_fst bc (mk_bext bc) wc e HW) as F1. pose proof (mk_sctx_c_ok bc (mk_bext bc) wc e HW) as F2.
    destruct (mk_sctx_c bc (mk_bext bc) wc e) as [sp wc']. cbn [fst snd] in *. subst sp. exists wc'. split; [reflexivity|exact F2].
  - rewrite HS. exists wc. split; [reflexivity|exact HW].
Qed.

Lemma sym_stepBIF_cr_spec : forall segs bc kx c xm rm i ss scr, KXOK kx -> BASFK.BCOK bc c -> XMOK bc xm -> BASFK.RMOK bc rm ->
  let r := sym_stepBIF_cr bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
             (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c xm rm segs i ss scr in
  fst (fst (fst r)) = sym_stepBI bc kx segs i ss scr /\ BASFK.BCOK bc (snd (fst (fst r))) /\ XMOK bc (snd (fst r)) /\ BASFK.RMOK bc (snd r).
Proof.
  intros segs bc kx c xm rm i ss scr HK HC HX HR.
  set (lis := map (mk_sctx bc (mk_bext bc)) (s_log ss)). set (lia := map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)).
  set (gl := GLof (mk_sctx bc (mk_bext bc)) (s_log ss)).
  assert (DF : let r := (sym_stepBIF_cx bc kx (mk_xc segs kx) (mk_bext bc) lis lia gl c xm segs i ss scr, rm) in
               fst (fst (fst r)) = sym_stepBI bc kx segs i ss scr /\ BASFK.BCOK bc (snd (fst (fst r))) /\ XMOK bc (snd (fst r)) /\ BASFK.RMOK bc (snd r)).
  { cbv zeta. cbn [fst snd]. destruct (sym_stepBIF_cx_spec bc kx (mk_xc segs kx) (mk_bext bc) lis lia gl c xm segs i ss scr HX) as [E1 E2].
    destruct (sym_stepBIF_c_spec bc kx segs c i ss scr HK HC) as [E3 E4]. fold lis lia gl in E3, E4.
    rewrite E1. split; [exact E3|]. split; [exact E4|]. split; [exact E2|exact HR]. }
  assert (MEMO : forall rd e, sym_stepBI bc kx segs i ss scr = SOk (ssetF ss rd (BASFK.foldKBG bc e) (s_pc ss + 4)) [] scr ->
            let r := (let '(v, rm') := BASFK.foldKBM bc rm e in (SOk (ssetF ss rd v (s_pc ss + 4)) [] scr, c, xm, rm')) in
            fst (fst (fst r)) = sym_stepBI bc kx segs i ss scr /\ BASFK.BCOK bc (snd (fst (fst r))) /\ XMOK bc (snd (fst r)) /\ BASFK.RMOK bc (snd r)).
  { intros rd e HE. destruct (BASFK.foldKBM_ok bc rm e HR) as [F1 F2]. destruct (BASFK.foldKBM bc rm e) as [v rm']. cbn [fst snd] in *. subst v.
    split; [symmetry; exact HE|]. split; [exact HC|]. split; [exact HX|exact F2]. }
  pose proof (sym_stepBIF_eq bc kx segs i ss scr HK) as GEN. fold lis in GEN.
  unfold sym_stepBIF_cr. cbv zeta. fold lis lia gl.
  destruct i; try exact DF;
    repeat match goal with |- context [if BASFK.bigE ?x then _ else _] => destruct (BASFK.bigE x) end;
    first [exact DF | apply MEMO; rewrite <- GEN; reflexivity].
Qed.
Lemma sym_stepXBIFx_spec : forall segs bc kx c xm rm K i ss scr, KXOK kx -> bc = mkbc (bc_fk bc) -> BASFK.BCOK bc c -> XMOK bc xm -> BASFK.RMOK bc rm ->
  let r := sym_stepXBIFx segs bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
             (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c xm rm K i ss scr in
  fst (fst (fst r)) = sym_stepXBI segs bc kx K i ss scr /\ BASFK.BCOK bc (snd (fst (fst r))) /\ XMOK bc (snd (fst r)) /\ BASFK.RMOK bc (snd r).
Proof.
  intros segs bc kx c xm rm K i ss scr HK HB HC HX HR. cbv zeta. unfold sym_stepXBIFx, sym_stepXBI.
  destruct (sym_stepBIF_cr_spec segs bc kx c xm rm i ss scr HK HC HX HR) as (E & O1 & O2 & O3).
  destruct (sym_stepBIF_cr bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
              (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c xm rm segs i ss scr) as [[[r c'] xm'] rm'].
  cbn [fst snd] in *. subst r. split; [|split; [exact O1|split; [exact O2|exact O3]]].
  destruct (sym_stepBI bc kx segs i ss scr) as [ss' scs scr'|] eqn:E; [|reflexivity].
  rewrite (step_next_mono _ _ _ _ _ _ _ _ _ E), (x_filterBF_eq segs bc ss ss' scs HB). reflexivity.
Qed.
Lemma sym_execTXBIF_go_eq : forall segs bc kx t K fuel first stops ss ck wc c xm rm,
  KXOK kx -> bc = mkbc (bc_fk bc) -> WCOK bc (mk_bext bc) wc -> BASFK.BCOK bc c -> XMOK bc xm -> BASFK.RMOK bc rm ->
  sym_execTXBIF_go segs bc kx (mk_xc segs kx) (mk_bext bc) t K fuel first stops ss (map (mk_sctx bc (mk_bext bc)) (s_log ss))
    (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss))
    ck (map (mk_sctx bc (mk_bext bc)) (s_log ck)) (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ck))
    (GLof (mk_sctx bc (mk_bext bc)) (s_log ck)) wc c xm rm (mk_stt stops)
  = (sym_execTXBI_go segs bc kx t K fuel first stops ss ck,
     map (mk_sctx bc (mk_bext bc)) (s_log (sym_execTXBI_go segs bc kx t K fuel first stops ss ck))).
Proof.
  intros segs bc kx t K fuel. induction fuel as [|f IH]; intros first stops ss ck wc c xm rm HK HB HW HC HX HR.
  - cbn [sym_execTXBIF_go sym_execTXBI_go]. destruct (s_clean ss); reflexivity.
  - cbn [sym_execTXBIF_go sym_execTXBI_go]. rewrite is_stopF_eq.
    replace (if first then false else existsb (Z.eqb (s_pc ss)) stops) with (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool by (destruct first; reflexivity).
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); reflexivity|].
    destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); reflexivity].
    destruct (sym_stepXBIFx_spec segs bc kx c xm rm K i ss scr_nil HK HB HC HX HR) as (EX & OX & OM & OR).
    destruct (sym_stepXBIFx segs bc kx (mk_xc segs kx) (mk_bext bc) (map (mk_sctx bc (mk_bext bc)) (s_log ss))
                (map (fun e => sann_sp (mk_sctx bc (mk_bext bc) e) e) (s_log ss)) (GLof (mk_sctx bc (mk_bext bc)) (s_log ss)) c xm rm K i ss scr_nil) as [[[r c'] xm'] rm'].
    cbn [fst snd] in EX, OX, OM, OR. subst r.
    destruct (sym_stepXBI segs bc kx K i ss scr_nil) as [ss' [|sc scs] scr'|] eqn:E; try (destruct (s_clean ss); reflexivity).
    destruct (lupd_ok _ _ _ _ _ _ _ _ _ _ wc E HW) as [wc' [L1 L2]].
    destruct (is_store_instr i) eqn:IS.
    + rewrite L1. destruct (s_clean ss'); apply IH; assumption.
    + unfold lupd in L1. rewrite IS in L1. injection L1 as L1a L1b L1c L1d. rewrite L1a, L1b, L1c.
      destruct (s_clean ss'); apply IH; assumption.
Qed.
Lemma sym_execTXBIF_eq : forall segs bc kx t K fuel first stops ss, KXOK kx -> bc = mkbc (bc_fk bc) ->
  sym_execTXBIF segs bc kx (mk_xc segs kx) (mk_bext bc) t K fuel first stops ss
  = (sym_execTXBI segs bc kx t K fuel first stops ss,
     map (mk_sctx bc (mk_bext bc)) (s_log (sym_execTXBI segs bc kx t K fuel first stops ss))).
Proof.
  intros. unfold sym_execTXBIF, sym_execTXBI. cbv zeta.
  change (s_log ss) with (s_log (clr ss)). apply sym_execTXBIF_go_eq; [assumption|assumption|apply WCOK_empty|apply BASFK.BCOK_nil|apply XMOK_nil|apply BASFK.RMOK_nil].
Qed.

Lemma stepx_nokx : forall segs bc kx xc kx' xc' ex lis lia gl c xm rm K i ss scr, needs_kx i = false ->
  sym_stepXBIFx segs bc kx xc ex lis lia gl c xm rm K i ss scr = sym_stepXBIFx segs bc kx' xc' ex lis lia gl c xm rm K i ss scr.
Proof.
  intros segs bc kx xc kx' xc' ex lis lia gl c xm rm K i ss scr H. unfold sym_stepXBIFx, sym_stepBIF_cr, sym_stepBIF_cx.
  destruct i; try discriminate; reflexivity.
Qed.
Lemma sym_execTXBIF_goL_eq : forall segs bc kn ex t K fuel okx first stops ss lis lia gl ck cklis cklia ckgl wc c xm rm stt,
  (okx = None \/ okx = Some (BLKFK.mk_kix_f kn, mk_xc segs (BLKFK.mk_kix_f kn))) ->
  sym_execTXBIF_goL segs bc kn okx ex t K fuel first stops ss lis lia gl ck cklis cklia ckgl wc c xm rm stt
  = sym_execTXBIF_go segs bc (BLKFK.mk_kix_f kn) (mk_xc segs (BLKFK.mk_kix_f kn)) ex t K fuel first stops ss lis lia gl ck cklis cklia ckgl wc c xm rm stt.
Proof.
  intros segs bc kn ex t K fuel. induction fuel as [|f IH]; intros okx first stops ss lis lia gl ck cklis cklia ckgl wc c xm rm stt HO; [reflexivity|].
  cbn [sym_execTXBIF_goL sym_execTXBIF_go].
  destruct (if first then false else is_stopF stt stops (s_pc ss)); [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  set (KX0 := BLKFK.mk_kix_f kn) in *. set (XC0 := mk_xc segs KX0) in *.
  assert (G : exists okx', (okx' = None \/ okx' = Some (KX0, XC0)) /\
              (let '(kx, xc, okx1) := if needs_kx i then match okx with Some (kx, xc) => (kx, xc, okx) | None => (KX0, XC0, Some (KX0, XC0)) end else (kx_nil, xc_nil, okx) in
               (sym_stepXBIFx segs bc kx xc ex lis lia gl c xm rm K i ss scr_nil, okx1))
              = (sym_stepXBIFx segs bc KX0 XC0 ex lis lia gl c xm rm K i ss scr_nil, okx')).
  { destruct (needs_kx i) eqn:NK.
    - destruct HO as [->| ->]; exists (Some (KX0, XC0)); (split; [right; reflexivity|reflexivity]).
    - exists okx. split; [exact HO|]. rewrite (stepx_nokx segs bc kx_nil xc_nil KX0 XC0 ex lis lia gl c xm rm K i ss scr_nil NK). reflexivity. }
  destruct G as (okx' & HO' & GE).
  destruct (if needs_kx i then match okx with Some (kx, xc) => (kx, xc, okx) | None => (KX0, XC0, Some (KX0, XC0)) end else (kx_nil, xc_nil, okx)) as [[kx xc] okx1].
  injection GE as GE1 GE2. subst okx1. rewrite GE1.
  destruct (sym_stepXBIFx segs bc KX0 XC0 ex lis lia gl c xm rm K i ss scr_nil) as [[[r c'] xm'] rm'].
  destruct r as [ss' [|sc scs] scr'|]; try reflexivity.
  destruct (is_store_instr i).
  - destruct (lupd bc ex i ss' lis lia gl wc) as [[[lis' lia'] gl'] wc']. destruct (s_clean ss'); apply IH; exact HO'.
  - destruct (s_clean ss'); apply IH; exact HO'.
Qed.
Lemma sym_execTXBIFL_eq : forall segs bc kn ex t K fuel first stops ss,
  sym_execTXBIFL segs bc kn ex t K fuel first stops ss
  = sym_execTXBIF segs bc (BLKFK.mk_kix_f kn) (mk_xc segs (BLKFK.mk_kix_f kn)) ex t K fuel first stops ss.
Proof. intros. unfold sym_execTXBIFL, sym_execTXBIF. cbv zeta. apply sym_execTXBIF_goL_eq. left. reflexivity. Qed.
Lemma run_block_f_eq : forall segs IT nx0 K fuel stops cs, run_block_f segs IT nx0 K fuel stops cs = run_block segs IT nx0 K fuel stops cs.
Proof.
  intros. unfold run_block_f, run_block. rewrite sym_execTXBIFL_eq. rewrite BLKFK.fresh_ok_f_eq, BLKFK.mkbc_m_eq, BLKFK.mk_kix_f_eq. destruct (fresh_ok nx0 cs); [|reflexivity]. cbv zeta.
  rewrite sym_execTXBIF_eq by (first [reflexivity | eexists; reflexivity]). rewrite carryKF_ctx_eq, carryKF_eq. reflexivity.
Qed.
Theorem run_block_gc_f_eq : forall segs IT nx0 K fuel stops cs,
  run_block_gc_f segs IT nx0 K fuel stops cs = run_block_gc segs IT nx0 K fuel stops cs.
Proof. intros. unfold run_block_gc_f, run_block_gc. rewrite run_block_f_eq. destruct (run_block segs IT nx0 K fuel stops cs); [rewrite BLKFK.cs_gc_b_eq|]; reflexivity. Qed.

End EXFK.
