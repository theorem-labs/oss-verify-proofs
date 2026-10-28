(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SeqExec Hoare.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module XIA.
Definition SB : Z := 0x7fff8000.
Definition LOWEND : Z := 0x7fff7fff.
Definition HIGHBEG : Z := 0x10007fff8000.
Definition HIGHEND : Z := 0x7fffffffffff.
Definition SCR : Z := 2560.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition app8 (p n : Z) : Prop := (0 <= p /\ p + n + 8 <= LOWEND) \/ (HIGHBEG <= p /\ p + n + 8 <= HIGHEND).
(* [comment removed for export] *)
Definition shadow_ok (M : word -> option byte) (p n : Z) : Prop :=
  (forall x : word, SB + p / 8 <= bv_unsigned x < SB + (p + n - 1) / 8 -> M x = Some (Z_to_bv 8 0)) /\
  (exists k, M (Z_to_bv 64 (SB + (p + n - 1) / 8)) = Some (Z_to_bv 8 k) /\ (k = 0 \/ (p + n - 1) mod 8 < k <= 7)) /\
  (n <= 64 -> forall x : word, 8 * ((SB + p / 8) / 8) <= bv_unsigned x < 8 * ((SB + (p + n - 1) / 8) / 8) + 8 -> M x <> None).

Section WithImage.
Variable segs : list Segment.
Variable MSET : Z.                        (* [comment removed for export] *)
Variable MCPY : Z.                        (* [comment removed for export] *)
Variable CELLS : list (Z * nat * Z).      (* [comment removed for export] *)
(* [comment removed for export] *)
Variable TLSPC : Z.
Variable TCELLS : list (Z * nat * Z).
Variable TPV ENTV CTXSLOT BLKSLOT : Z.

Definition cells_ok (M : word -> option byte) : Prop :=
  Forall (fun c : Z * nat * Z => let '(a, w, v) := c in
            rdn segs M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v))) CELLS.

(* [comment removed for export] *)
Definition icpt_fill_spec : Prop :=
  forall (fx : FPState) (mem0 : word -> option byte) (c : word) (pd n sp : Z) (regs : bvmap 5 word) (ret : word),
    1 <= n <= 2 ^ 40 -> app8 pd n ->
    0x1000000 <= sp - SCR -> sp < 2 ^ 64 ->
    SB + (pd + n - 1) / 8 + 8 <= sp - SCR ->
    (pd + n <= sp - SCR \/ sp <= pd) ->
    store_ok segs mem0 (Z_to_bv 64 (sp - SCR)) (Z.to_nat SCR) = true ->
    store_ok segs mem0 (Z_to_bv 64 pd) (Z.to_nat n) = true ->
    cells_ok mem0 -> shadow_ok mem0 pd n ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = Z_to_bv 64 sp ->
    getr regs 10%bv = Z_to_bv 64 pd -> getr regs 11%bv = c -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs' Mj,
      msteps segs (@mkst fx regs (Z_to_bv 64 MSET) mem0 (seg_rom segs))
                  (@mkst fx regs' ret (wbytes Mj (Z_to_bv 64 pd) (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) (seg_rom segs))
      /\ APSX.kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 pd
      /\ (forall x : word, bv_unsigned x < sp - SCR \/ sp <= bv_unsigned x -> Mj x = mem0 x)
      /\ mem_grows mem0 Mj.

(* [comment removed for export] *)
Definition icpt_copy_spec : Prop :=
  forall (fx : FPState) (mem0 : word -> option byte) (pd ps n sp : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    1 <= n <= 2 ^ 40 -> length bs = Z.to_nat n -> app8 pd n -> app8 ps n ->
    0x1000000 <= sp - SCR -> sp < 2 ^ 64 ->
    SB + (pd + n - 1) / 8 + 8 <= sp - SCR -> SB + (ps + n - 1) / 8 + 8 <= sp - SCR ->
    (pd + n <= sp - SCR \/ sp <= pd) -> (ps + n <= sp - SCR \/ sp <= ps) -> (pd + n <= ps \/ ps + n <= pd) ->
    store_ok segs mem0 (Z_to_bv 64 (sp - SCR)) (Z.to_nat SCR) = true ->
    store_ok segs mem0 (Z_to_bv 64 pd) (Z.to_nat n) = true ->
    rdn segs mem0 (Z_to_bv 64 ps) (Z.to_nat n) = Some bs ->
    cells_ok mem0 -> shadow_ok mem0 pd n -> shadow_ok mem0 ps n ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = Z_to_bv 64 sp ->
    getr regs 10%bv = Z_to_bv 64 pd -> getr regs 11%bv = Z_to_bv 64 ps -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs' Mj,
      msteps segs (@mkst fx regs (Z_to_bv 64 MCPY) mem0 (seg_rom segs))
                  (@mkst fx regs' ret (wbytes Mj (Z_to_bv 64 pd) bs) (seg_rom segs))
      /\ APSX.kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 pd
      /\ (forall x : word, bv_unsigned x < sp - SCR \/ sp <= bv_unsigned x -> Mj x = mem0 x)
      /\ mem_grows mem0 Mj.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition has_cells (k : list kentry) : bool :=
  forallb (fun c : Z * nat * Z => let '(a, w, v) := c in
             (Z.leb 0 a && Z.ltb (a + Z.of_nat w) (2 ^ 64) && Z.leb 0 v && Z.ltb v (2 ^ 64)
              && existsb (APC.kentry_eqb (KWord (SA (ELit 0) a) w (ELit v))) k)%bool) CELLS.

(* [comment removed for export] *)
Definition shz_entry (b : expr) (dk nlo nhi : Z) (K : kentry) : bool :=
  let s7 := if Z.ltb 64 nlo then 0 else 7 in let s8 := if Z.ltb 64 nlo then 1 else 8 in   (* [comment removed for export] *)
  match K with
  | KZero (SA (EAlu ALU_SRL zb (ELit 3)) zo) (ELit zl) =>
      (expr_eqb zb b && Z.leb 0 zl && Z.ltb zl (2 ^ 64) && Z.leb zo (SB + dk / 8 - s7) && Z.leb (SB + (dk + nhi - 1) / 8 + s8) (zo + zl))%bool
  | KZero (SA (ELit 0) zo) (ELit zl) =>
      (expr_eqb b (ELit 0) && Z.leb 0 zl && Z.ltb zl (2 ^ 64) && Z.leb zo (SB + dk / 8 - s7) && Z.leb (SB + (dk + nhi - 1) / 8 + s8) (zo + zl))%bool
  | _ => false
  end.
Definition shz_cover (fk k : list kentry) (b : expr) (dk nlo nhi : Z) : bool :=
  match lin_lowbits_kn fk b 3 with
  | Some 0 => existsb (shz_entry b dk nlo nhi) k
  | _ => false
  end.

Definition xmemset (F : list SGP.region) (ss : sym_state) : option sym_state :=
  let k := s_know ss in let fk := facts_of k in let nx := s_next ss in
  if negb (Z.eqb (s_pc ss) MSET) then None else
  if negb (SR.closed ss []) then None else
  match SR.ret_lit ss, SR.reg ss 11 with
  | Some ret, ELit c0 =>
      let ne := SR.reg ss 12 in let c8 := (c0 mod two64) mod 256 in
      let dst := SR.reg ss 10 in let '(db, dk) := split_lit dst in
      let esp := SR.reg ss 2 in let '(sb, sk) := split_lit esp in
      match xlo fk ne, xhi fk ne, xlo fk dst, xhi fk dst, xlo fk esp, xhi fk esp with
      | Some nlo, Some nhi, Some dlo, Some dhi, Some slo, Some shi =>
          if (Z.leb 1 nlo && Z.leb nhi (2 ^ 40)
              && (Z.leb (dhi + nhi + 8) LOWEND || (Z.leb HIGHBEG dlo && Z.leb (dhi + nhi + 8) HIGHEND))
              && Z.leb (0x1000000 + SCR) slo && Z.ltb shi (2 ^ 64)
              && Z.leb (SB + (dhi + nhi - 1) / 8 + 8) (slo - SCR)
              && APC.flat_x fk db dk ne && APC.kwritable_x fk k db dk ne && SGP.withinE fk F db dk ne
              && APC.flat_x fk sb (sk - SCR) (ELit SCR) && APC.kwritable_x fk k sb (sk - SCR) (ELit SCR) && SGP.withinE fk F sb (sk - SCR) (ELit SCR)
              && ranges_apart_x fk db dk ne sb (sk - SCR) (ELit SCR)
              && has_cells k && shz_cover fk k db dk nlo nhi)%bool
          then let k1 := APC.kn_havoc k sb (sk - SCR) (ELit SCR) in
               let k' := (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: APC.kn_havoc k1 db dk ne in
               if APC.kn_vars_lt nx k' then Some (SR.after_call ss ret dst k') else None
          else None
      | _, _, _, _, _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition app8b (lo hi n : Z) : bool := (Z.leb (hi + n + 8) LOWEND || (Z.leb HIGHBEG lo && Z.leb (hi + n + 8) HIGHEND))%bool.

(* [comment removed for export] *)
Definition xmemcpy (F : list SGP.region) (ss : sym_state) : option sym_state :=
  let k := s_know ss in let fk := facts_of k in let nx := s_next ss in
  if negb (Z.eqb (s_pc ss) MCPY) then None else
  if negb (SR.closed ss []) then None else
  match SR.ret_lit ss, SR.reg ss 12 with
  | Some ret, ELit n0 =>
      let n := n0 mod two64 in
      let dst := SR.reg ss 10 in let src := SR.reg ss 11 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      let esp := SR.reg ss 2 in let '(pb, pk) := split_lit esp in
      match xlo fk dst, xhi fk dst, xlo fk src, xhi fk src, xlo fk esp, xhi fk esp with
      | Some dlo, Some dhi, Some slo, Some shi, Some plo, Some phi =>
          if (Z.ltb 0 n && Z.leb n 2048 && app8b dlo dhi n && app8b slo shi n
              && Z.leb (0x1000000 + SCR) plo && Z.ltb phi (2 ^ 64)
              && Z.leb (SB + (dhi + n - 1) / 8 + 8) (plo - SCR) && Z.leb (SB + (shi + n - 1) / 8 + 8) (plo - SCR)
              && APC.flat_x fk db dk (ELit n) && APC.flat_x fk sb sk (ELit n)
              && APC.kwritable_x fk k db dk (ELit n) && SGP.withinE fk F db dk (ELit n)
              && ranges_apart_x fk db dk (ELit n) sb sk (ELit n)
              && APC.flat_x fk pb (pk - SCR) (ELit SCR) && APC.kwritable_x fk k pb (pk - SCR) (ELit SCR) && SGP.withinE fk F pb (pk - SCR) (ELit SCR)
              && ranges_apart_x fk db dk (ELit n) pb (pk - SCR) (ELit SCR) && ranges_apart_x fk sb sk (ELit n) pb (pk - SCR) (ELit SCR)
              && has_cells k && shz_cover fk k db dk n n && shz_cover fk k sb sk n n)%bool
          then match APC.copy_facts segs (Z.to_nat n) k sb sk db dk n with
               | Some kc =>
                   let k1 := APC.kn_havoc k pb (pk - SCR) (ELit SCR) in
                   let k' := kc ++ APC.kn_havoc (SR.kimg_precut k1 db dk n) db dk (ELit n) in
                   if APC.kn_vars_lt nx k' then Some (SR.after_call ss ret dst k') else None
               | None => None
               end
          else None
      | _, _, _, _, _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SCRT : Z := 512.          (* [comment removed for export] *)
Definition u64cell (M : word -> option byte) (a v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
Definition tcells_ok (M : word -> option byte) : Prop :=
  Forall (fun c : Z * nat * Z => let '(a, w, v) := c in
            rdn segs M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v))) TCELLS.
Definition apartZ (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.

(* [comment removed for export] *)
Definition icpt_tls_spec : Prop :=
  forall (fx : FPState) (mem0 : word -> option byte) (d off ctx th tbv tev blk rec sp : Z) (regs : bvmap 5 word) (ret : word),
    0x1000000 <= sp - SCRT -> sp < 2 ^ 64 ->
    0 <= d -> d + 16 <= 2 ^ 64 -> 0 <= off < 2 ^ 64 ->
    0 < ctx -> ctx + 160 <= 2 ^ 64 -> 0 < th -> th + 64 <= 2 ^ 64 -> 0 <= tbv < 2 ^ 64 -> 0 <= tev < 2 ^ 64 ->
    0 < blk -> blk + 4080 <= 2 ^ 64 - 1 -> 0 < rec < 2 ^ 64 ->
    store_ok segs mem0 (Z_to_bv 64 (sp - SCRT)) (Z.to_nat SCRT) = true ->
    tcells_ok mem0 ->
    u64cell mem0 d 1 -> u64cell mem0 (d + 8) off ->
    u64cell mem0 CTXSLOT ctx -> u64cell mem0 (ctx + 152) th -> u64cell mem0 (th + 48) tbv -> u64cell mem0 (th + 56) tev ->
    u64cell mem0 BLKSLOT blk -> u64cell mem0 (blk + 24) rec ->
    apartZ d 16 (sp - SCRT) SCRT -> apartZ (ctx + 152) 8 (sp - SCRT) SCRT -> apartZ (th + 48) 16 (sp - SCRT) SCRT -> apartZ (blk + 24) 8 (sp - SCRT) SCRT ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = Z_to_bv 64 sp -> getr regs 4%bv = Z_to_bv 64 TPV -> getr regs 10%bv = Z_to_bv 64 d ->
    exists regs' Mj,
      msteps segs (@mkst fx regs (Z_to_bv 64 TLSPC) mem0 (seg_rom segs)) (@mkst fx regs' ret Mj (seg_rom segs))
      /\ APSX.kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 ((ENTV + off) mod 2 ^ 64)
      /\ (forall x : word, bv_unsigned x < sp - SCRT \/ sp <= bv_unsigned x -> Mj x = mem0 x)
      /\ mem_grows mem0 Mj.

Definition has_tcells (k : list kentry) : bool :=
  forallb (fun c : Z * nat * Z => let '(a, w, v) := c in
             (Z.leb 0 a && Z.ltb (a + Z.of_nat w) (2 ^ 64) && Z.leb 0 v && Z.ltb v (2 ^ 64)
              && existsb (APC.kentry_eqb (KWord (SA (ELit 0) a) w (ELit v))) k)%bool) TCELLS.
(* [comment removed for export] *)
Fixpoint find_cell8 (kn : list kentry) (b : expr) (o : Z) : option expr :=
  match kn with
  | [] => None
  | KWord (SA b' o') w' v :: r => if (expr_eqb b' b && Z.eqb o' o && Nat.eqb w' 8)%bool then Some v else find_cell8 r b o
  | _ :: r => find_cell8 r b o
  end.
(* [comment removed for export] *)
Definition obj_ok (fk : list kentry) (e : expr) (room co cn : Z) (pb : expr) (pk : Z) : bool :=
  let '(b, o) := split_lit e in
  match xlo fk e with
  | Some lo => (Z.leb 1 lo && APC.flat_x fk b o (ELit room) && ranges_apart_x fk b (o + co) (ELit cn) pb (pk - SCRT) (ELit SCRT))%bool
  | None => false
  end.

Definition xtls (F : list SGP.region) (ss : sym_state) : option sym_state :=
  let k := s_know ss in let fk := facts_of k in let nx := s_next ss in
  if negb (Z.eqb (s_pc ss) TLSPC) then None else
  if negb (SR.closed ss []) then None else
  match SR.ret_lit ss with
  | Some ret =>
      let '(db, dk) := split_lit (SR.reg ss 10) in
      let esp := SR.reg ss 2 in let '(pb, pk) := split_lit esp in
      match xlo fk esp, xhi fk esp, find_cell8 k db dk, find_cell8 k db (dk + 8), find_cell8 k (ELit 0) CTXSLOT, find_cell8 k (ELit 0) BLKSLOT with
      | Some plo, Some phi, Some (ELit 1), Some (ELit off), Some ectx, Some eblk =>
          let '(cb, ck) := split_lit ectx in let '(bb, bk) := split_lit eblk in
          match find_cell8 k cb (ck + 152), find_cell8 k bb (bk + 24) with
          | Some eth, Some erec =>
              let '(tb, tk) := split_lit eth in
              match find_cell8 k tb (tk + 48), find_cell8 k tb (tk + 56), xlo fk erec with
              | Some _, Some _, Some rlo =>
                  if (expr_eqb (SR.reg ss 4) (ELit TPV) && Z.leb 0 TPV && Z.ltb TPV (2 ^ 64)
                      && Z.leb 0 off && Z.ltb off (2 ^ 64) && Z.leb 1 rlo
                      && Z.leb (0x1000000 + SCRT) plo && Z.ltb phi (2 ^ 64)
                      && APC.flat_x fk pb (pk - SCRT) (ELit SCRT) && APC.kwritable_x fk k pb (pk - SCRT) (ELit SCRT) && SGP.withinE fk F pb (pk - SCRT) (ELit SCRT)
                      && APC.flat_x fk db dk (ELit 16) && ranges_apart_x fk db dk (ELit 16) pb (pk - SCRT) (ELit SCRT)
                      && obj_ok fk ectx 160 152 8 pb pk && obj_ok fk eth 64 48 16 pb pk && obj_ok fk eblk 4081 24 8 pb pk
                      && has_tcells k)%bool
                  then let k' := APC.kn_havoc k pb (pk - SCRT) (ELit SCRT) in
                       if APC.kn_vars_lt nx k' then Some (SR.after_call ss ret (ELit ((ENTV + off) mod 2 ^ 64)) k') else None
                  else None
              | _, _, _ => None
              end
          | _, _ => None
          end
      | _, _, _, _, _, _ => None
      end
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma has_cells_sound : forall E M k, know_ok segs E M k -> has_cells k = true -> cells_ok M.
Proof.
  intros E M k HK H. unfold has_cells in H. unfold cells_ok. rewrite forallb_forall in H. apply Forall_forall.
  intros [[a w] v] Hin. specialize (H _ Hin). cbn beta iota in H.
  repeat (apply andb_true_iff in H as [H ?X]).
  apply Z.leb_le in H. apply Z.ltb_lt in X2. apply Z.leb_le in X1. apply Z.ltb_lt in X0.
  apply existsb_exists in X as (K & HKin & HKe). apply APS.kentry_eqb_eq in HKe. subst K.
  pose proof (proj1 (Forall_forall _ _) HK _ HKin) as HKo. cbn [kentry_ok] in HKo. destruct HKo as (_ & _ & Hrd).
  rewrite APSX.adenot_SA in Hrd. unfold estart in Hrd. cbn [a_base a_off edenot] in Hrd.
  rewrite u64_of_Z in Hrd by lia. rewrite Z.add_0_l in Hrd. exact Hrd.
Qed.

Lemma div8_add : forall u d, u mod 8 = 0 -> (u + d) / 8 = u / 8 + d / 8.
Proof.
  intros u d Hu. pose proof (Z.div_mod u 8 ltac:(lia)) as E. rewrite Hu, Z.add_0_r in E.
  rewrite E at 1. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity.
Qed.

Lemma shz_cover_sound : forall E M fk k b dk nlo nhi n,
  know_ok segs E M fk -> know_ok segs E M k -> shz_cover fk k b dk nlo nhi = true ->
  1 <= n -> nlo <= n <= nhi -> 0 <= bv_unsigned (edenot E b) + dk ->
  shadow_ok M (bv_unsigned (edenot E b) + dk) n.
Proof.
  intros E M fk k b dk nlo nhi n HKf HK H Hn1 Hn Hlo. unfold shz_cover in H.
  destruct (lin_lowbits_kn fk b 3) as [lb|] eqn:Hlb; [|discriminate].
  destruct lb; try discriminate.
  destruct (lin_lowbits_kn_sound segs E M fk b 3 0 HKf ltac:(lia) Hlb) as [Hal _]. change (2 ^ 3) with 8 in Hal.
  apply existsb_exists in H as (K & HKin & HKe).
  set (u := bv_unsigned (edenot E b)) in *.
  set (s7 := if Z.ltb 64 nlo then 0 else 7) in *. set (s8 := if Z.ltb 64 nlo then 1 else 8) in *.
  assert (ZZ : exists zo zl, zo <= SB + dk / 8 - s7 /\ SB + (dk + nhi - 1) / 8 + s8 <= zo + zl /\ 0 <= u / 8 + zo /\ u / 8 + zo + zl <= 2 ^ 64
                /\ forall x : word, u / 8 + zo <= bv_unsigned x < u / 8 + zo + zl -> M x = Some (Z_to_bv 8 0)).
  { pose proof (proj1 (Forall_forall _ _) HK _ HKin) as HKo.
    unfold shz_entry in HKe. fold s7 s8 in HKe.
    destruct K as [| [zbx zo] zl | | | | | | | |]; try discriminate.
    destruct zbx as [z0| |op zb z3| | | | |]; try discriminate.
    - (* [comment removed for export] *)
      destruct z0 as [|?|?]; try discriminate.
      destruct zl as [zl| | | | | | |]; try discriminate.
      cbn [kentry_ok] in HKo. destruct HKo as (Hfl & Hz).
      unfold elenZ in Hz, Hfl. cbn [edenot] in Hz, Hfl.
      repeat (apply andb_true_iff in HKe as [HKe ?X]).
      apply expr_eqb_eq in HKe. apply Z.leb_le in X2. apply Z.ltb_lt in X1. apply Z.leb_le in X0. apply Z.leb_le in X.
      rewrite u64_of_Z in Hz, Hfl by lia.
      unfold flat, estart in Hfl. unfold estart in Hz. cbn [a_base a_off edenot] in Hz, Hfl.
      change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hz, Hfl.
      assert (Eu : u = 0) by (subst u; rewrite HKe; reflexivity).
      exists zo, zl. rewrite Eu. change (0 / 8) with 0. repeat split; try lia.
      intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). replace (bv_unsigned x) with (0 + zo + (bv_unsigned x - zo)) by lia.
      apply Hz. lia.
    - (* [comment removed for export] *)
      destruct op; try discriminate.
      destruct z3 as [z| | | | | | |]; try discriminate. destruct z as [|p|]; try discriminate.
      destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate.
      destruct zl as [zl| | | | | | |]; try discriminate.
      cbn [kentry_ok] in HKo. destruct HKo as (Hfl & Hz).
      unfold elenZ in Hz, Hfl. cbn [edenot] in Hz, Hfl.
      repeat (apply andb_true_iff in HKe as [HKe ?X]).
      apply expr_eqb_eq in HKe. subst zb. apply Z.leb_le in X2. apply Z.ltb_lt in X1. apply Z.leb_le in X0. apply Z.leb_le in X.
      rewrite u64_of_Z in Hz, Hfl by lia.
      unfold flat, estart in Hfl. unfold estart in Hz. cbn [a_base a_off] in Hz, Hfl.
      rewrite (u_srl_lit E b 3) in Hz, Hfl. change (2 ^ ((3 mod two64) mod 64)) with 8 in Hz, Hfl. fold u in Hz, Hfl.
      exists zo, zl. repeat split; try lia.
      intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). replace (bv_unsigned x) with (u / 8 + zo + (bv_unsigned x - (u / 8 + zo))) by lia.
      apply Hz. lia. }
  destruct ZZ as (zo & zl & Z1 & Z2 & Z3 & Z4 & ZZ).
  assert (Dv1 : (u + dk) / 8 = u / 8 + dk / 8) by (apply div8_add; exact Hal).
  assert (Dv2 : (u + dk + n - 1) / 8 = u / 8 + (dk + n - 1) / 8) by (replace (u + dk + n - 1) with (u + (dk + n - 1)) by lia; apply div8_add; exact Hal).
  assert (Mono : (dk + n - 1) / 8 <= (dk + nhi - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (Mono2 : dk / 8 <= (dk + n - 1) / 8) by (apply Z.div_le_mono; lia).
  set (fD := SB + (u + dk) / 8) in *. set (lD := SB + (u + dk + n - 1) / 8) in *.
  assert (EfD : fD = SB + u / 8 + dk / 8) by (subst fD; lia). assert (ElD : lD = SB + u / 8 + (dk + n - 1) / 8) by (subst lD; lia).
  pose proof (Z.div_mod fD 8 ltac:(lia)) as DMf. pose proof (Z.mod_pos_bound fD 8 ltac:(lia)) as MBf.
  pose proof (Z.div_mod lD 8 ltac:(lia)) as DMl. pose proof (Z.mod_pos_bound lD 8 ltac:(lia)) as MBl.
  assert (S78 : 0 <= s7 /\ 1 <= s8) by (subst s7 s8; destruct (Z.ltb 64 nlo); lia).
  unfold shadow_ok. fold fD lD. split; [|split].
  - intros x Hx. apply ZZ. lia.
  - exists 0. split; [|left; reflexivity]. apply ZZ. rewrite u64_of_Z by lia. lia.
  - intros Hn64 x Hx. assert (E78 : s7 = 7 /\ s8 = 8) by (subst s7 s8; destruct (Z.ltb_spec 64 nlo); [lia | split; reflexivity]).
    rewrite ZZ; [discriminate|]. lia.
Qed.

Lemma reg_sound2 : forall E ss R, regs_ok E (s_regs ss) R -> getr R 2%bv = edenot E (SR.reg ss 2).
Proof. intros E ss R HR. exact (HR 2%bv). Qed.

Hypothesis FILL : icpt_fill_spec.

Lemma xmemset_ok : forall nx0 BR F M0 (fx : FPState) ss ss' E R Mc,
  forallb (SGP.region_vars_lt nx0) F = true ->
  SGP.bfacts_vars_lt BR nx0 = true ->
  xmemset F ss = Some ss' -> SGP.INV2 segs nx0 BR F M0 E ss R Mc ->
  exists (fx' : FPState) E' R' Mc',
    env_agree (s_next ss) E E' /\ SGP.INV2 segs nx0 BR F M0 E' ss' R' Mc'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs))
                   (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) Mc' (seg_rom segs)).
Proof.
  intros nx0 BR F M0 fx ss ss' E R Mc Fvars BRvars H HI.
  pose proof (SGP.i_regs _ _ _ _ _ _ _ _ _ HI) as HR. pose proof (SGP.i_know _ _ _ _ _ _ _ _ _ HI) as HK.
  unfold xmemset in H.
  destruct (Z.eqb (s_pc ss) MSET) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (SR.closed ss []) eqn:Hcl; [|discriminate]. cbn [negb] in H.
  pose proof Hcl as Hcl0. unfold SR.closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (SR.ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (SR.reg ss 11) as [c0| | | | | | |] eqn:H11; try discriminate.
  destruct (split_lit (SR.reg ss 10)) as [db dk] eqn:Hsd.
  destruct (split_lit (SR.reg ss 2)) as [sb sk] eqn:Hssp.
  destruct (xlo (facts_of (s_know ss)) (SR.reg ss 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xlo (facts_of (s_know ss)) (SR.reg ss 10)) as [dlo|] eqn:Hdlo; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xlo (facts_of (s_know ss)) (SR.reg ss 2)) as [slo|] eqn:Hslo; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 2)) as [shi|] eqn:Hshi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection H as <-.
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into Hshz. rename X0 into Hcells. rename X1 into Hap. rename X2 into Hins. rename X3 into Hwrs. rename X4 into Hfs.
  rename X5 into Hin. rename X6 into Hwr. rename X7 into Hfd. rename X8 into Hshd. rename X9 into Hshi64. rename X10 into Hslo'.
  rename X11 into Happ. rename X12 into Hn40.
  apply Z.leb_le in Hc. apply Z.leb_le in Hn40. apply Z.leb_le in Hslo'. apply Z.ltb_lt in Hshi64. apply Z.leb_le in Hshd.
  set (ne := SR.reg ss 12) in *. set (c8 := ((c0 mod two64) mod 256)%Z) in *.
  set (k := s_know ss) in *. set (fk := facts_of k) in *.
  pose proof (facts_of_ok segs E Mc k HK) as HKf. fold fk in HKf.
  set (nv := elenZ E ne).
  pose proof (xlo_sound segs E Mc fk ne nlo HKf Hnlo) as Xlo. pose proof (xhi_sound segs E Mc fk ne nhi HKf Hnhi) as Xhi.
  change (bv_unsigned (edenot E ne)) with nv in Xlo, Xhi.
  destruct (APSX.w_flat_x_sound segs E Mc fk db dk ne HKf Hfd) as (Dlo & Dhi & Dpos).
  destruct (APSX.kwritable_x_sound segs E Mc fk k db dk ne HKf HK Hwr) as (Wst & _ & _).
  destruct (APSX.w_flat_x_sound segs E Mc fk sb (sk - SCR) (ELit SCR) HKf Hfs) as (Slo & Shi & _).
  destruct (APSX.kwritable_x_sound segs E Mc fk k sb (sk - SCR) (ELit SCR) HKf HK Hwrs) as (Wss & _ & _).
  pose proof (ranges_apart_x_sound segs E Mc fk db dk ne sb (sk - SCR) (ELit SCR) HKf Hap) as Hapart.
  assert (HlenS : elenZ E (ELit SCR) = SCR) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; unfold SCR; lia).
  change (bv_unsigned (edenot E ne)) with nv in Dhi, Dpos. fold nv in Wst, Hapart.
  change (bv_unsigned (edenot E (ELit SCR))) with (elenZ E (ELit SCR)) in Shi. rewrite HlenS in *.
  set (D := estart E (SA db dk)) in *. set (W := estart E (SA sb (sk - SCR))) in *.
  (* [comment removed for export] *)
  destruct (SR.ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  pose proof (SR.reg_sound10 E ss R HR) as R10. pose proof (SR.reg_sound11 E ss R HR) as R11.
  pose proof (SR.reg_sound12 E ss R HR) as R12. fold ne in R12. rewrite H11 in R11. cbn [edenot] in R11.
  pose proof (reg_sound2 E ss R HR) as R2.
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd) in R10. change (bv_unsigned (edenot E db) + dk)%Z with D in R10.
  pose proof (xlo_sound segs E Mc fk (SR.reg ss 10) dlo HKf Hdlo) as XDl. pose proof (xhi_sound segs E Mc fk (SR.reg ss 10) dhi HKf Hdhi) as XD.
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd) in XD, XDl. change (bv_unsigned (edenot E db) + dk)%Z with D in XD, XDl.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Dpos; lia).
  rewrite u64_of_Z in XD, XDl by exact HD64.
  pose proof (xlo_sound segs E Mc fk (SR.reg ss 2) slo HKf Hslo) as XSl. pose proof (xhi_sound segs E Mc fk (SR.reg ss 2) shi HKf Hshi) as XSh.
  set (spv := bv_unsigned (edenot E (SR.reg ss 2))) in *.
  assert (Hspv : spv = W + SCR).
  { subst spv W. rewrite (APSX.w_split_lit_denot E (SR.reg ss 2) sb sk Hssp). unfold estart. cbn [a_base a_off].
    rewrite (APSX.w_split_lit_denot E (SR.reg ss 2) sb sk Hssp) in XSl.
    unfold estart in Slo, Shi. cbn [a_base a_off] in Slo, Shi.
    destruct (Z.eq_dec (bv_unsigned (edenot E sb) + sk) (2 ^ 64)) as [E64|N64].
    - exfalso. rewrite E64 in XSl. change (bv_unsigned (Z_to_bv 64 (2 ^ 64))) with 0 in XSl. clear - XSl Hslo'. unfold SCR in *. lia.
    - rewrite u64_of_Z; unfold SCR in *; lia. }
  assert (R2' : getr R 2%bv = Z_to_bv 64 spv) by (rewrite R2; subst spv; symmetry; apply Z_to_bv_bv_unsigned).
  assert (R12' : getr R 12%bv = Z_to_bv 64 nv) by (rewrite R12; symmetry; apply Z_to_bv_bv_unsigned).
  assert (A1 : 1 <= nv <= 2 ^ 40) by (clear - Hc Xlo Hn40 Xhi; lia).
  assert (Aapp : app8 D nv).
  { unfold app8. apply orb_true_iff in Happ as [Ha|Ha].
    - apply Z.leb_le in Ha. left. clear - Ha XD Xhi HD64. lia.
    - apply andb_true_iff in Ha as [Ha1 Ha2]. apply Z.leb_le in Ha1. apply Z.leb_le in Ha2. right. clear - Ha1 Ha2 XD XDl Xhi. lia. }
  assert (Ash : SB + (D + nv - 1) / 8 + 8 <= spv - SCR).
  { assert ((D + nv - 1) / 8 <= (dhi + nhi - 1) / 8) by (apply Z.div_le_mono; clear - XD Xhi; lia). clear - H Hshd XSl. lia. }
  assert (Adj : D + nv <= spv - SCR \/ spv <= D) by (clear - Hapart Hspv; lia).
  assert (Aws : store_ok segs Mc (Z_to_bv 64 (spv - SCR)) (Z.to_nat SCR) = true).
  { replace (spv - SCR) with W by (clear - Hspv; lia). apply Wss. rewrite Z2Nat.id by (unfold SCR; lia). clear. lia. }
  assert (Awd : store_ok segs Mc (Z_to_bv 64 D) (Z.to_nat nv) = true) by (apply Wst; clear - A1; lia).
  pose proof (has_cells_sound E Mc k HK Hcells) as Acells.
  assert (Ashz : shadow_ok Mc D nv).
  { subst D. unfold estart. cbn [a_base a_off]. eapply shz_cover_sound; [exact HKf | exact HK | exact Hshz | clear - A1; lia | clear - A1 Xlo Xhi; lia | ].
    unfold estart in Dlo. cbn [a_base a_off] in Dlo. exact Dlo. }
  destruct (FILL fx Mc (Z_to_bv 64 c0) D nv spv R (Z_to_bv 64 ret) A1 Aapp ltac:(clear - Hslo' XSl; lia) ltac:(clear - XSh Hshi64; lia) Ash Adj Aws Awd Acells Ashz
              Hrok R1 R2' R10 R11 R12') as (regs' & Mj & Hms & Hkept & Ha0 & Hout & Hgr).
  assert (Hc8 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 c0)) = Z_to_bv 8 c8).
  { subst c8. rewrite APSX.Z_to_bv8_mod. f_equal; try (rewrite Z_to_bv_unsigned; reflexivity). }
  rewrite Hc8 in Hms.
  set (nx := s_next ss) in *.
  set (M' := wbytes Mj (Z_to_bv 64 D) (repeat (Z_to_bv 8 c8) (Z.to_nat nv))) in *.
  exists fx, (APSX.ext_call E nx regs'), regs', M'.
  pose proof (APSX.ext_call_agree E nx regs') as Hag.
  split; [exact Hag|].
  assert (Fdst : APC.expr_vars_lt nx (SR.reg ss 10) = true) by (unfold SR.reg; apply SR.nth_sr_vars_lt; [exact Fsr0 | lia]).
  assert (Fne : APC.expr_vars_lt nx ne = true) by (unfold ne, SR.reg; apply SR.nth_sr_vars_lt; [exact Fsr0 | lia]).
  pose proof (APSX.split_lit_vars _ _ _ _ Hsd Fdst) as Fdb.
  assert (FILLED : forall i, 0 <= i < nv -> M' (Z_to_bv 64 (D + i)) = Some (Z_to_bv 8 c8)).
  { intros i Hi. subst M'. rewrite <- (u64_of_Z D HD64) at 2. apply APSX.wbytes_fill_at; [rewrite (u64_of_Z D HD64); clear - Dhi; lia | exact Hi]. }
  assert (OUT : forall x : word, bv_unsigned x < D \/ D + nv <= bv_unsigned x -> M' x = Mj x).
  { intros x Hx. subst M'. apply wbytes_out; rewrite ?repeat_length, ?Z2Nat.id, ?u64_of_Z by lia; clear - Hx A1 HD64 Dhi; lia. }
  assert (OUTW : forall x : word, bv_unsigned x < W \/ W + SCR <= bv_unsigned x -> Mj x = Mc x).
  { intros x Hx. apply Hout. clear - Hx Hspv. lia. }
  pose proof (APS.env_agree_le nx0 nx E _ Hag (SGP.i_nx _ _ _ _ _ _ _ _ _ HI)) as Hag0.
  split.
  - constructor.
    + cbn [SR.after_call s_regs s_next].
      apply (APSX.regs_after_call E (s_regs ss) R regs' nx (Some (SR.reg ss 10)) HR Fsr0 Hkept).
      split; [exact Fdst|]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0.
      rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd). reflexivity.
    + cbn [SR.after_call s_know].
      eapply APS.know_ok_agree'; [exact Hag | exact Hkv |].
      constructor.
      * destruct (Z.eqb c8 0) eqn:Hz; cbn [kentry_ok]; unfold flat; fold nv; change (estart E (SA db dk)) with D.
        -- apply Z.eqb_eq in Hz. split; [clear - HD64 Dhi A1; lia|]. intros i Hi. rewrite (FILLED i Hi), Hz. reflexivity.
        -- split; [clear - HD64 Dhi A1; lia|]. intros i Hi. exact (FILLED i Hi).
      * eapply APSX.w_know_ok_havoc; [ | | apply wbytes_grows].
        -- eapply APSX.w_know_ok_havoc; [exact HK | | exact Hgr]. intros x Hx. rewrite HlenS in Hx. apply OUTW. exact Hx.
        -- intros x Hx. apply OUT. exact Hx.
    + intros a Ha. cbn [SR.after_call s_know] in *.
      pose proof (SGP.outside_agree nx0 F Fvars E _ a Hag0 Ha) as HaE.
      rewrite OUT.
      * rewrite OUTW; [apply (SGP.i_frame _ _ _ _ _ _ _ _ _ HI); exact HaE|].
        destruct (SGP.withinE_sound segs F E Mc fk sb (sk - SCR) (ELit SCR) HKf (SGP.i_flat _ _ _ _ _ _ _ _ _ HI) Hins) as (rb & rlo & rlen & Hrin & H1 & H2).
        rewrite HlenS in H2. fold W in H1, H2.
        pose proof (proj1 (Forall_forall _ _) HaE _ Hrin) as Hout'. cbn beta iota in Hout'. clear - Hout' H1 H2. lia.
      * destruct (SGP.withinE_sound segs F E Mc fk db dk ne HKf (SGP.i_flat _ _ _ _ _ _ _ _ _ HI) Hin) as (rb & rlo & rlen & Hrin & H1 & H2).
        fold nv D in H1, H2.
        pose proof (proj1 (Forall_forall _ _) HaE _ Hrin) as Hout'. cbn beta iota in Hout'. clear - Hout' H1 H2. lia.
    + eapply mem_grows_trans; [exact (SGP.i_grows _ _ _ _ _ _ _ _ _ HI)|]. eapply mem_grows_trans; [exact Hgr | apply wbytes_grows].
    + eapply SGP.regions_ok_agree; [exact Fvars | exact Hag0 | exact (SGP.i_flat _ _ _ _ _ _ _ _ _ HI)].
    + cbn [SR.after_call s_next]. pose proof (SGP.i_nx _ _ _ _ _ _ _ _ _ HI). lia.
    + eapply SGP.bfacts_agree; [exact BRvars | exact Hag0 | exact (SGP.i_bf _ _ _ _ _ _ _ _ _ HI)].
  - cbn [SR.after_call s_pc]. rewrite Hpc. exact Hms.
Qed.

Lemma app8b_sound : forall lo hi n p, app8b lo hi n = true -> lo <= p <= hi -> 0 <= p -> app8 p n.
Proof.
  intros lo hi n p H Hp Hp0. unfold app8b in H. unfold app8. apply orb_true_iff in H as [Ha|Ha].
  - apply Z.leb_le in Ha. left. lia.
  - apply andb_true_iff in Ha as [Ha1 Ha2]. apply Z.leb_le in Ha1. apply Z.leb_le in Ha2. right. lia.
Qed.

Hypothesis COPY : icpt_copy_spec.

Lemma xmemcpy_ok : forall nx0 BR F M0 (fx : FPState) ss ss' E R Mc,
  forallb (SGP.region_vars_lt nx0) F = true ->
  SGP.bfacts_vars_lt BR nx0 = true ->
  xmemcpy F ss = Some ss' -> SGP.INV2 segs nx0 BR F M0 E ss R Mc ->
  exists (fx' : FPState) E' R' Mc',
    env_agree (s_next ss) E E' /\ SGP.INV2 segs nx0 BR F M0 E' ss' R' Mc'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs))
                   (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) Mc' (seg_rom segs)).
Proof.
  intros nx0 BR F M0 fx ss ss' E R Mc Fvars BRvars H HI.
  pose proof (SGP.i_regs _ _ _ _ _ _ _ _ _ HI) as HR. pose proof (SGP.i_know _ _ _ _ _ _ _ _ _ HI) as HK.
  unfold xmemcpy in H.
  destruct (Z.eqb (s_pc ss) MCPY) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (SR.closed ss []) eqn:Hcl; [|discriminate]. cbn [negb] in H.
  pose proof Hcl as Hcl0. unfold SR.closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (SR.ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (SR.reg ss 12) as [n0| | | | | | |] eqn:H12; try discriminate.
  destruct (split_lit (SR.reg ss 10)) as [db dk] eqn:Hsd. destruct (split_lit (SR.reg ss 11)) as [sb sk] eqn:Hss.
  destruct (split_lit (SR.reg ss 2)) as [pb pk] eqn:Hssp.
  destruct (xlo (facts_of (s_know ss)) (SR.reg ss 10)) as [dlo|] eqn:Hdlo; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xlo (facts_of (s_know ss)) (SR.reg ss 11)) as [slo|] eqn:Hslo; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 11)) as [shi|] eqn:Hshi; [|discriminate].
  destruct (xlo (facts_of (s_know ss)) (SR.reg ss 2)) as [plo|] eqn:Hplo; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 2)) as [phi|] eqn:Hphi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (APC.copy_facts segs (Z.to_nat (n0 mod two64)) (s_know ss) sb sk db dk (n0 mod two64)) as [kc|] eqn:Hcf; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection H as <-.
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into HshzS. rename X0 into HshzD. rename X1 into Hcells. rename X2 into HapSW. rename X3 into HapDW. rename X4 into Hins.
  rename X5 into Hwrs. rename X6 into Hfw. rename X7 into HapDS. rename X8 into Hin. rename X9 into Hwr. rename X10 into Hfs. rename X11 into Hfd.
  rename X12 into HshS. rename X13 into HshD. rename X14 into Hphi64. rename X15 into Hplo'. rename X16 into HappS. rename X17 into HappD. rename X18 into Hn2048.
  apply Z.ltb_lt in Hc. apply Z.leb_le in Hn2048. apply Z.leb_le in Hplo'. apply Z.ltb_lt in Hphi64. apply Z.leb_le in HshD. apply Z.leb_le in HshS.
  set (n := (n0 mod two64)%Z) in *. set (k := s_know ss) in *. set (fk := facts_of k) in *.
  assert (Hn64 : 0 <= n < two64) by (subst n; unfold two64; apply Z.mod_pos_bound; lia).
  assert (Hndef : n = (n0 mod two64)%Z) by reflexivity. clearbody n. unfold two64 in Hn64.
  pose proof (facts_of_ok segs E Mc k HK) as HKf. fold fk in HKf.
  assert (Hlen : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  assert (HlenS : elenZ E (ELit SCR) = SCR) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; unfold SCR; lia).
  destruct (APSX.w_flat_x_sound segs E Mc fk db dk (ELit n) HKf Hfd) as (Dlo & Dhi & _).
  destruct (APSX.w_flat_x_sound segs E Mc fk sb sk (ELit n) HKf Hfs) as (Slo & Shi & _).
  destruct (APSX.w_flat_x_sound segs E Mc fk pb (pk - SCR) (ELit SCR) HKf Hfw) as (Wlo & Whi & _).
  destruct (APSX.kwritable_x_sound segs E Mc fk k db dk (ELit n) HKf HK Hwr) as (Wst & _ & _).
  destruct (APSX.kwritable_x_sound segs E Mc fk k pb (pk - SCR) (ELit SCR) HKf HK Hwrs) as (Wss & _ & _).
  pose proof (ranges_apart_x_sound segs E Mc fk db dk (ELit n) sb sk (ELit n) HKf HapDS) as HapartDS.
  pose proof (ranges_apart_x_sound segs E Mc fk db dk (ELit n) pb (pk - SCR) (ELit SCR) HKf HapDW) as HapartDW.
  pose proof (ranges_apart_x_sound segs E Mc fk sb sk (ELit n) pb (pk - SCR) (ELit SCR) HKf HapSW) as HapartSW.
  change (bv_unsigned (edenot E (ELit n))) with (elenZ E (ELit n)) in Dhi, Shi.
  change (bv_unsigned (edenot E (ELit SCR))) with (elenZ E (ELit SCR)) in Whi.
  rewrite Hlen, HlenS in *.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *. set (W := estart E (SA pb (pk - SCR))) in *.
  destruct (APSX.copy_facts_sound segs E Mc k sb db (Z.to_nat n) sk dk n kc HK Hcf ltac:(lia) ltac:(lia) Slo Shi Dlo Dhi)
    as (bs & Hlbs & Hrd & Hkc).
  fold S in Hrd. fold D in Hkc.
  (* [comment removed for export] *)
  destruct (SR.ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  pose proof (SR.reg_sound10 E ss R HR) as R10. pose proof (SR.reg_sound11 E ss R HR) as R11.
  pose proof (SR.reg_sound12 E ss R HR) as R12. rewrite H12 in R12. cbn [edenot] in R12.
  pose proof (reg_sound2 E ss R HR) as R2.
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd) in R10. rewrite (APSX.w_split_lit_denot E (SR.reg ss 11) sb sk Hss) in R11.
  change (bv_unsigned (edenot E db) + dk)%Z with D in R10. change (bv_unsigned (edenot E sb) + sk)%Z with S in R11.
  pose proof (xlo_sound segs E Mc fk (SR.reg ss 10) dlo HKf Hdlo) as XDl. pose proof (xhi_sound segs E Mc fk (SR.reg ss 10) dhi HKf Hdhi) as XD.
  pose proof (xlo_sound segs E Mc fk (SR.reg ss 11) slo HKf Hslo) as XSl. pose proof (xhi_sound segs E Mc fk (SR.reg ss 11) shi HKf Hshi) as XS.
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd) in XD, XDl. rewrite (APSX.w_split_lit_denot E (SR.reg ss 11) sb sk Hss) in XS, XSl.
  change (bv_unsigned (edenot E db) + dk)%Z with D in XD, XDl. change (bv_unsigned (edenot E sb) + sk)%Z with S in XS, XSl.
  pose proof (app8b_sound dlo dhi n) as AD0. pose proof (app8b_sound slo shi n) as AS0.
  assert (HD64 : 0 <= D < 2 ^ 64).
  { split; [exact Dlo|]. destruct (Z.eq_dec D (2 ^ 64)) as [E64|N64]; [|clear - Dhi Hc N64; lia]. exfalso. clear - Dhi Hc E64. lia. }
  assert (HS64 : 0 <= S < 2 ^ 64).
  { split; [exact Slo|]. clear - Shi Hc. lia. }
  rewrite u64_of_Z in XD, XDl by exact HD64. rewrite u64_of_Z in XS, XSl by exact HS64.
  pose proof (xlo_sound segs E Mc fk (SR.reg ss 2) plo HKf Hplo) as XPl. pose proof (xhi_sound segs E Mc fk (SR.reg ss 2) phi HKf Hphi) as XPh.
  set (spv := bv_unsigned (edenot E (SR.reg ss 2))) in *.
  assert (Hspv : spv = W + SCR).
  { subst spv W. rewrite (APSX.w_split_lit_denot E (SR.reg ss 2) pb pk Hssp). unfold estart. cbn [a_base a_off].
    rewrite (APSX.w_split_lit_denot E (SR.reg ss 2) pb pk Hssp) in XPl.
    unfold estart in Wlo, Whi. cbn [a_base a_off] in Wlo, Whi.
    destruct (Z.eq_dec (bv_unsigned (edenot E pb) + pk) (2 ^ 64)) as [E64|N64].
    - exfalso. rewrite E64 in XPl. change (bv_unsigned (Z_to_bv 64 (2 ^ 64))) with 0 in XPl. clear - XPl Hplo'. unfold SCR in *. lia.
    - rewrite u64_of_Z; unfold SCR in *; lia. }
  assert (R2' : getr R 2%bv = Z_to_bv 64 spv) by (rewrite R2; subst spv; symmetry; apply Z_to_bv_bv_unsigned).
  assert (R12' : getr R 12%bv = Z_to_bv 64 n).
  { rewrite R12. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite Hndef. unfold two64, bv_wrap.
    change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_mod by lia. reflexivity. }
  assert (A1 : 1 <= n <= 2 ^ 40) by (clear - Hc Hn2048; lia).
  assert (AappD : app8 D n) by (apply AD0; [exact HappD | clear - XD XDl; lia | clear - HD64; lia]).
  assert (AappS : app8 S n) by (apply AS0; [exact HappS | clear - XS XSl; lia | clear - HS64; lia]).
  assert (AshD : SB + (D + n - 1) / 8 + 8 <= spv - SCR).
  { assert ((D + n - 1) / 8 <= (dhi + n - 1) / 8) by (apply Z.div_le_mono; clear - XD; lia). clear - H HshD XPl. lia. }
  assert (AshS : SB + (S + n - 1) / 8 + 8 <= spv - SCR).
  { assert ((S + n - 1) / 8 <= (shi + n - 1) / 8) by (apply Z.div_le_mono; clear - XS; lia). clear - H HshS XPl. lia. }
  assert (AdjD : D + n <= spv - SCR \/ spv <= D) by (clear - HapartDW Hspv; lia).
  assert (AdjS : S + n <= spv - SCR \/ spv <= S) by (clear - HapartSW Hspv; lia).
  assert (Aws : store_ok segs Mc (Z_to_bv 64 (spv - SCR)) (Z.to_nat SCR) = true).
  { replace (spv - SCR) with W by (clear - Hspv; lia). apply Wss. rewrite Z2Nat.id by (unfold SCR; lia). clear. lia. }
  assert (Awd : store_ok segs Mc (Z_to_bv 64 D) (Z.to_nat n) = true) by (apply Wst; clear - A1; lia).
  pose proof (has_cells_sound E Mc k HK Hcells) as Acells.
  assert (AshzD : shadow_ok Mc D n).
  { subst D. unfold estart. cbn [a_base a_off]. eapply shz_cover_sound; [exact HKf | exact HK | exact HshzD | clear - A1; lia | clear; lia | ].
    unfold estart in Dlo. cbn [a_base a_off] in Dlo. exact Dlo. }
  assert (AshzS : shadow_ok Mc S n).
  { subst S. unfold estart. cbn [a_base a_off]. eapply shz_cover_sound; [exact HKf | exact HK | exact HshzS | clear - A1; lia | clear; lia | ].
    unfold estart in Slo. cbn [a_base a_off] in Slo. exact Slo. }
  destruct (COPY fx Mc D S n spv bs R (Z_to_bv 64 ret) A1 Hlbs AappD AappS ltac:(clear - Hplo' XPl; lia) ltac:(clear - XPh Hphi64; lia) AshD AshS AdjD AdjS
              ltac:(clear - HapartDS; lia) Aws Awd Hrd Acells AshzD AshzS Hrok R1 R2' R10 R11 R12') as (regs' & Mj & Hms & Hkept & Ha0 & Hout & Hgr).
  set (nx := s_next ss) in *.
  set (M' := wbytes Mj (Z_to_bv 64 D) bs) in *.
  exists fx, (APSX.ext_call E nx regs'), regs', M'.
  pose proof (APSX.ext_call_agree E nx regs') as Hag.
  split; [exact Hag|].
  assert (Fdst : APC.expr_vars_lt nx (SR.reg ss 10) = true) by (unfold SR.reg; apply SR.nth_sr_vars_lt; [exact Fsr0 | lia]).
  assert (OUT : forall x : word, bv_unsigned x < D \/ D + n <= bv_unsigned x -> M' x = Mj x).
  { intros x Hx. subst M'. apply wbytes_out; rewrite ?Hlbs, ?Z2Nat.id, ?u64_of_Z by lia; clear - Hx A1 HD64 Dhi; lia. }
  assert (OUTW : forall x : word, bv_unsigned x < W \/ W + SCR <= bv_unsigned x -> Mj x = Mc x).
  { intros x Hx. apply Hout. clear - Hx Hspv. lia. }
  pose proof (APS.env_agree_le nx0 nx E _ Hag (SGP.i_nx _ _ _ _ _ _ _ _ _ HI)) as Hag0.
  split.
  - constructor.
    + cbn [SR.after_call s_regs s_next].
      apply (APSX.regs_after_call E (s_regs ss) R regs' nx (Some (SR.reg ss 10)) HR Fsr0 Hkept).
      split; [exact Fdst|]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0.
      rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd). reflexivity.
    + cbn [SR.after_call s_know].
      eapply APS.know_ok_agree'; [exact Hag | exact Hkv |].
      apply Forall_app. split.
      * apply Hkc. subst M'. rewrite <- Hlbs. apply rdn_wbytes_hit. rewrite u64_of_Z by lia. rewrite Hlbs. rewrite Z2Nat.id by lia. clear - Dhi. lia.
      * eapply APSX.w_know_ok_havoc; [ | | apply wbytes_grows].
        -- apply SR.kimg_precut_ok. eapply APSX.w_know_ok_havoc; [exact HK | | exact Hgr]. intros x Hx. rewrite HlenS in Hx. apply OUTW. exact Hx.
        -- intros x Hx. rewrite Hlen in Hx. apply OUT. exact Hx.
    + intros a Ha. cbn [SR.after_call s_know] in *.
      pose proof (SGP.outside_agree nx0 F Fvars E _ a Hag0 Ha) as HaE.
      rewrite OUT.
      * rewrite OUTW; [apply (SGP.i_frame _ _ _ _ _ _ _ _ _ HI); exact HaE|].
        destruct (SGP.withinE_sound segs F E Mc fk pb (pk - SCR) (ELit SCR) HKf (SGP.i_flat _ _ _ _ _ _ _ _ _ HI) Hins) as (rb & rlo & rlen & Hrin & H1 & H2).
        rewrite HlenS in H2. fold W in H1, H2.
        pose proof (proj1 (Forall_forall _ _) HaE _ Hrin) as Hout'. cbn beta iota in Hout'. clear - Hout' H1 H2. lia.
      * destruct (SGP.withinE_sound segs F E Mc fk db dk (ELit n) HKf (SGP.i_flat _ _ _ _ _ _ _ _ _ HI) Hin) as (rb & rlo & rlen & Hrin & H1 & H2).
        rewrite Hlen in H2. fold D in H1, H2.
        pose proof (proj1 (Forall_forall _ _) HaE _ Hrin) as Hout'. cbn beta iota in Hout'. clear - Hout' H1 H2. lia.
    + eapply mem_grows_trans; [exact (SGP.i_grows _ _ _ _ _ _ _ _ _ HI)|]. eapply mem_grows_trans; [exact Hgr | apply wbytes_grows].
    + eapply SGP.regions_ok_agree; [exact Fvars | exact Hag0 | exact (SGP.i_flat _ _ _ _ _ _ _ _ _ HI)].
    + cbn [SR.after_call s_next]. pose proof (SGP.i_nx _ _ _ _ _ _ _ _ _ HI). lia.
    + eapply SGP.bfacts_agree; [exact BRvars | exact Hag0 | exact (SGP.i_bf _ _ _ _ _ _ _ _ _ HI)].
  - cbn [SR.after_call s_pc]. rewrite Hpc. exact Hms.
Qed.

(* [comment removed for export] *)
Lemma has_tcells_sound : forall E M k, know_ok segs E M k -> has_tcells k = true -> tcells_ok M.
Proof.
  intros E M k HK H. unfold has_tcells in H. unfold tcells_ok. rewrite forallb_forall in H. apply Forall_forall.
  intros [[a w] v] Hin. specialize (H _ Hin). cbn beta iota in H.
  repeat (apply andb_true_iff in H as [H ?X]).
  apply Z.leb_le in H. apply Z.ltb_lt in X2. apply Z.leb_le in X1. apply Z.ltb_lt in X0.
  apply existsb_exists in X as (K & HKin & HKe). apply APS.kentry_eqb_eq in HKe. subst K.
  pose proof (proj1 (Forall_forall _ _) HK _ HKin) as HKo. cbn [kentry_ok] in HKo. destruct HKo as (_ & _ & Hrd).
  rewrite APSX.adenot_SA in Hrd. unfold estart in Hrd. cbn [a_base a_off edenot] in Hrd.
  rewrite u64_of_Z in Hrd by lia. rewrite Z.add_0_l in Hrd. exact Hrd.
Qed.

Lemma find_cell8_sound : forall E M k b o v, know_ok segs E M k -> find_cell8 k b o = Some v ->
  rdn segs M (Z_to_bv 64 (estart E (SA b o))) 8%nat = Some (word_to_le_bytes 8 (edenot E v)).
Proof.
  intros E M k b o v HK. induction k as [|K r IH]; intros H; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hr]. cbn [find_cell8] in H.
  destruct K as [[b' o'] w' v'| | | | | | | | |]; try exact (IH Hr H).
  destruct (expr_eqb b' b && Z.eqb o' o && Nat.eqb w' 8)%bool eqn:Hm; [|exact (IH Hr H)].
  injection H as <-. apply andb_true_iff in Hm as [Hm Hw]. apply andb_true_iff in Hm as [Hb Ho].
  apply expr_eqb_eq in Hb. apply Z.eqb_eq in Ho. apply Nat.eqb_eq in Hw. subst b' o' w'.
  cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & Hrd). rewrite APSX.adenot_SA in Hrd. exact Hrd.
Qed.

Lemma u64cell_of : forall E M k b o v a, know_ok segs E M k -> find_cell8 k b o = Some v -> estart E (SA b o) = a ->
  u64cell M a (bv_unsigned (edenot E v)).
Proof.
  intros E M k b o v a HK H Ha. unfold u64cell. rewrite <- Ha, Z_to_bv_bv_unsigned. exact (find_cell8_sound E M k b o v HK H).
Qed.

Lemma obj_ok_sound : forall E M fk e room co cn pb pk b o,
  know_ok segs E M fk -> obj_ok fk e room co cn pb pk = true -> split_lit e = (b, o) -> 0 <= cn < 2 ^ 64 -> 0 <= room < 2 ^ 64 ->
  let v := bv_unsigned (edenot E e) in
  0 < v /\ v + room <= 2 ^ 64 /\ (forall c, estart E (SA b (o + c)) = v + c)
  /\ apartZ (v + co) cn (estart E (SA pb (pk - SCRT))) SCRT.
Proof.
  intros E M fk e room co cn pb pk b o HKf H Hsp Hcn Hroom v. unfold obj_ok in H. rewrite Hsp in H.
  destruct (xlo fk e) as [lo|] eqn:Hlo; [|discriminate].
  repeat (apply andb_true_iff in H as [H ?X]). apply Z.leb_le in H.
  pose proof (xlo_sound segs E M fk e lo HKf Hlo) as Xlo. fold v in Xlo.
  destruct (APSX.w_flat_x_sound segs E M fk b o (ELit room) HKf X0) as (Flo & Fhi & Fpos).
  unfold estart in Flo, Fhi. cbn [a_base a_off edenot] in Flo, Fhi, Fpos. rewrite u64_of_Z in Fhi, Fpos by lia.
  assert (Ev : v = bv_unsigned (edenot E b) + o).
  { subst v. rewrite (APSX.w_split_lit_denot E e b o Hsp). apply u64_of_Z. lia. }
  pose proof (ranges_apart_x_sound segs E M fk b (o + co) (ELit cn) pb (pk - SCRT) (ELit SCRT) HKf X) as Hap.
  assert (L1 : elenZ E (ELit cn) = cn) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  assert (L2 : elenZ E (ELit SCRT) = SCRT) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; unfold SCRT; lia).
  rewrite L1, L2 in Hap.
  assert (ES : forall c, estart E (SA b (o + c)) = v + c) by (intros c; unfold estart; cbn [a_base a_off]; lia).
  split; [lia|]. split; [lia|]. split; [exact ES|]. unfold apartZ. rewrite <- (ES co). exact Hap.
Qed.

Hypothesis TLS : icpt_tls_spec.

Lemma xtls_ok : forall nx0 BR F M0 (fx : FPState) ss ss' E R Mc,
  forallb (SGP.region_vars_lt nx0) F = true ->
  SGP.bfacts_vars_lt BR nx0 = true ->
  xtls F ss = Some ss' -> SGP.INV2 segs nx0 BR F M0 E ss R Mc ->
  exists (fx' : FPState) E' R' Mc',
    env_agree (s_next ss) E E' /\ SGP.INV2 segs nx0 BR F M0 E' ss' R' Mc'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) Mc (seg_rom segs))
                   (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) Mc' (seg_rom segs)).
Proof.
  intros nx0 BR F M0 fx ss ss' E R Mc Fvars BRvars H HI.
  pose proof (SGP.i_regs _ _ _ _ _ _ _ _ _ HI) as HR. pose proof (SGP.i_know _ _ _ _ _ _ _ _ _ HI) as HK.
  unfold xtls in H.
  destruct (Z.eqb (s_pc ss) TLSPC) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (SR.closed ss []) eqn:Hcl; [|discriminate]. cbn [negb] in H.
  pose proof Hcl as Hcl0. unfold SR.closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (SR.ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (SR.reg ss 10)) as [db dk] eqn:Hsd.
  destruct (split_lit (SR.reg ss 2)) as [pb pk] eqn:Hssp.
  destruct (xlo (facts_of (s_know ss)) (SR.reg ss 2)) as [plo|] eqn:Hplo; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (SR.reg ss 2)) as [phi|] eqn:Hphi; [|discriminate].
  destruct (find_cell8 (s_know ss) db dk) as [emd|] eqn:Cmd; [|discriminate].
  destruct emd as [zmd| | | | | | |]; try discriminate. destruct zmd as [|pmd|]; try discriminate. destruct pmd; try discriminate.
  destruct (find_cell8 (s_know ss) db (dk + 8)) as [eoff|] eqn:Coff; [|discriminate].
  destruct eoff as [off| | | | | | |]; try discriminate.
  destruct (find_cell8 (s_know ss) (ELit 0) CTXSLOT) as [ectx|] eqn:Cctx; [|discriminate].
  destruct (find_cell8 (s_know ss) (ELit 0) BLKSLOT) as [eblk|] eqn:Cblk; [|discriminate].
  destruct (split_lit ectx) as [cb ck] eqn:Hsc. destruct (split_lit eblk) as [bb bk] eqn:Hsb.
  destruct (find_cell8 (s_know ss) cb (ck + 152)) as [eth|] eqn:Cth; [|discriminate].
  destruct (find_cell8 (s_know ss) bb (bk + 24)) as [erec|] eqn:Crec; [|discriminate].
  destruct (split_lit eth) as [tb tk] eqn:Hst.
  destruct (find_cell8 (s_know ss) tb (tk + 48)) as [etb|] eqn:Ctb; [|discriminate].
  destruct (find_cell8 (s_know ss) tb (tk + 56)) as [ete|] eqn:Cte; [|discriminate].
  destruct (xlo (facts_of (s_know ss)) erec) as [rlo|] eqn:Hrlo; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection H as <-.
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into Htc. rename X0 into Oblk. rename X1 into Oth. rename X2 into Octx. rename X3 into HapD. rename X4 into HfD.
  rename X5 into Hins. rename X6 into Hwrs. rename X7 into Hfw. rename X8 into Hphi64. rename X9 into Hplo'. rename X10 into Hrlo'.
  rename X11 into Hoff2. rename X12 into Hoff1. rename X13 into Htp2. rename X14 into Htp1.
  apply expr_eqb_eq in Hc. apply Z.leb_le in Htp1. apply Z.ltb_lt in Htp2. apply Z.leb_le in Hoff1. apply Z.ltb_lt in Hoff2.
  apply Z.leb_le in Hrlo'. apply Z.leb_le in Hplo'. apply Z.ltb_lt in Hphi64.
  set (k := s_know ss) in *. set (fk := facts_of k) in *.
  pose proof (facts_of_ok segs E Mc k HK) as HKf. fold fk in HKf.
  assert (HlenS : elenZ E (ELit SCRT) = SCRT) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; unfold SCRT; lia).
  assert (Hlen16 : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  destruct (APSX.w_flat_x_sound segs E Mc fk pb (pk - SCRT) (ELit SCRT) HKf Hfw) as (Wlo & Whi & _).
  destruct (APSX.kwritable_x_sound segs E Mc fk k pb (pk - SCRT) (ELit SCRT) HKf HK Hwrs) as (Wss & _ & _).
  destruct (APSX.w_flat_x_sound segs E Mc fk db dk (ELit 16) HKf HfD) as (Dlo & Dhi & _).
  pose proof (ranges_apart_x_sound segs E Mc fk db dk (ELit 16) pb (pk - SCRT) (ELit SCRT) HKf HapD) as HapartD.
  change (bv_unsigned (edenot E (ELit SCRT))) with (elenZ E (ELit SCRT)) in Whi. change (bv_unsigned (edenot E (ELit 16))) with (elenZ E (ELit 16)) in Dhi.
  rewrite HlenS, Hlen16 in *.
  set (D := estart E (SA db dk)) in *. set (W := estart E (SA pb (pk - SCRT))) in *.
  destruct (obj_ok_sound E Mc fk ectx 160 152 8 pb pk cb ck HKf Octx Hsc ltac:(lia) ltac:(lia)) as (C1 & C2 & C3 & C4).
  destruct (obj_ok_sound E Mc fk eth 64 48 16 pb pk tb tk HKf Oth Hst ltac:(lia) ltac:(lia)) as (T1 & T2 & T3 & T4).
  destruct (obj_ok_sound E Mc fk eblk 4081 24 8 pb pk bb bk HKf Oblk Hsb ltac:(lia) ltac:(lia)) as (B1 & B2 & B3 & B4).
  fold W in C4, T4, B4.
  set (ctx := bv_unsigned (edenot E ectx)) in *. set (th := bv_unsigned (edenot E eth)) in *. set (blk := bv_unsigned (edenot E eblk)) in *.
  set (rec := bv_unsigned (edenot E erec)). set (tbv := bv_unsigned (edenot E etb)). set (tev := bv_unsigned (edenot E ete)).
  pose proof (xlo_sound segs E Mc fk erec rlo HKf Hrlo) as Xrec. fold rec in Xrec.
  pose proof (u64_range (edenot E erec)) as Rrec. pose proof (u64_range (edenot E etb)) as Rtb. pose proof (u64_range (edenot E ete)) as Rte.
  fold rec in Rrec. fold tbv in Rtb. fold tev in Rte.
  (* [comment removed for export] *)
  assert (Q1 : u64cell Mc D 1).
  { pose proof (u64cell_of E Mc k db dk (ELit 1) D HK Cmd eq_refl) as X. cbn [edenot] in X. rewrite u64_of_Z in X by lia. exact X. }
  assert (Q2 : u64cell Mc (D + 8) off).
  { pose proof (u64cell_of E Mc k db (dk + 8) (ELit off) (D + 8) HK Coff ltac:(subst D; unfold estart; cbn [a_base a_off]; lia)) as X.
    cbn [edenot] in X. rewrite u64_of_Z in X by lia. exact X. }
  assert (Q3 : u64cell Mc CTXSLOT ctx).
  { apply (u64cell_of E Mc k (ELit 0) CTXSLOT ectx CTXSLOT HK Cctx). unfold estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0. lia. }
  assert (Q4 : u64cell Mc (ctx + 152) th) by (apply (u64cell_of E Mc k cb (ck + 152) eth (ctx + 152) HK Cth); apply C3).
  assert (Q5 : u64cell Mc (th + 48) tbv) by (apply (u64cell_of E Mc k tb (tk + 48) etb (th + 48) HK Ctb); apply T3).
  assert (Q6 : u64cell Mc (th + 56) tev) by (apply (u64cell_of E Mc k tb (tk + 56) ete (th + 56) HK Cte); apply T3).
  assert (Q7 : u64cell Mc BLKSLOT blk).
  { apply (u64cell_of E Mc k (ELit 0) BLKSLOT eblk BLKSLOT HK Cblk). unfold estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0. lia. }
  assert (Q8 : u64cell Mc (blk + 24) rec) by (apply (u64cell_of E Mc k bb (bk + 24) erec (blk + 24) HK Crec); apply B3).
  (* [comment removed for export] *)
  destruct (SR.ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  pose proof (SR.reg_sound10 E ss R HR) as R10. pose proof (reg_sound2 E ss R HR) as R2.
  assert (R4 : getr R 4%bv = Z_to_bv 64 TPV) by (rewrite (HR 4%bv); change (sr_get (s_regs ss) 4%bv) with (SR.reg ss 4); rewrite Hc; reflexivity).
  rewrite (APSX.w_split_lit_denot E (SR.reg ss 10) db dk Hsd) in R10. change (bv_unsigned (edenot E db) + dk)%Z with D in R10.
  pose proof (xlo_sound segs E Mc fk (SR.reg ss 2) plo HKf Hplo) as XPl. pose proof (xhi_sound segs E Mc fk (SR.reg ss 2) phi HKf Hphi) as XPh.
  set (spv := bv_unsigned (edenot E (SR.reg ss 2))) in *.
  assert (Hspv : spv = W + SCRT).
  { subst spv W. rewrite (APSX.w_split_lit_denot E (SR.reg ss 2) pb pk Hssp). unfold estart. cbn [a_base a_off].
    rewrite (APSX.w_split_lit_denot E (SR.reg ss 2) pb pk Hssp) in XPl.
    unfold estart in Wlo, Whi. cbn [a_base a_off] in Wlo, Whi.
    destruct (Z.eq_dec (bv_unsigned (edenot E pb) + pk) (2 ^ 64)) as [E64|N64].
    - exfalso. rewrite E64 in XPl. change (bv_unsigned (Z_to_bv 64 (2 ^ 64))) with 0 in XPl. clear - XPl Hplo'. unfold SCRT in *. lia.
    - rewrite u64_of_Z; unfold SCRT in *; lia. }
  assert (R2' : getr R 2%bv = Z_to_bv 64 spv) by (rewrite R2; subst spv; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Aws : store_ok segs Mc (Z_to_bv 64 (spv - SCRT)) (Z.to_nat SCRT) = true).
  { replace (spv - SCRT) with W by (clear - Hspv; lia). apply Wss. rewrite Z2Nat.id by (unfold SCRT; lia). clear. lia. }
  pose proof (has_tcells_sound E Mc k HK Htc) as Atc.
  assert (AW : spv - SCRT = W) by (clear - Hspv; lia).
  destruct (TLS fx Mc D off ctx th tbv tev blk rec spv R (Z_to_bv 64 ret)
              ltac:(clear - Hplo' XPl; lia) ltac:(clear - XPh Hphi64; lia) ltac:(exact Dlo) ltac:(exact Dhi) ltac:(clear - Hoff1 Hoff2; lia)
              C1 ltac:(clear - C2; lia) T1 ltac:(clear - T2; lia) Rtb Rte B1 ltac:(clear - B2; lia) ltac:(clear - Xrec Hrlo' Rrec; lia)
              Aws Atc Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8
              ltac:(rewrite AW; exact HapartD) ltac:(rewrite AW; exact C4) ltac:(rewrite AW; exact T4) ltac:(rewrite AW; exact B4)
              Hrok R1 R2' R4 R10) as (regs' & Mj & Hms & Hkept & Ha0 & Hout & Hgr).
  set (nx := s_next ss) in *.
  exists fx, (APSX.ext_call E nx regs'), regs', Mj.
  pose proof (APSX.ext_call_agree E nx regs') as Hag.
  split; [exact Hag|].
  assert (OUTW : forall x : word, bv_unsigned x < W \/ W + SCRT <= bv_unsigned x -> Mj x = Mc x).
  { intros x Hx. apply Hout. clear - Hx Hspv. lia. }
  pose proof (APS.env_agree_le nx0 nx E _ Hag (SGP.i_nx _ _ _ _ _ _ _ _ _ HI)) as Hag0.
  split.
  - constructor.
    + cbn [SR.after_call s_regs s_next].
      apply (APSX.regs_after_call E (s_regs ss) R regs' nx (Some (ELit ((ENTV + off) mod 2 ^ 64))) HR Fsr0 Hkept).
      split; [reflexivity|]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0. reflexivity.
    + cbn [SR.after_call s_know].
      eapply APS.know_ok_agree'; [exact Hag | exact Hkv |].
      eapply APSX.w_know_ok_havoc; [exact HK | | exact Hgr]. intros x Hx. rewrite HlenS in Hx. apply OUTW. exact Hx.
    + intros a Ha. cbn [SR.after_call s_know] in *.
      pose proof (SGP.outside_agree nx0 F Fvars E _ a Hag0 Ha) as HaE.
      rewrite OUTW; [apply (SGP.i_frame _ _ _ _ _ _ _ _ _ HI); exact HaE|].
      destruct (SGP.withinE_sound segs F E Mc fk pb (pk - SCRT) (ELit SCRT) HKf (SGP.i_flat _ _ _ _ _ _ _ _ _ HI) Hins) as (rb & rlo' & rlen & Hrin & H1 & H2).
      rewrite HlenS in H2. fold W in H1, H2.
      pose proof (proj1 (Forall_forall _ _) HaE _ Hrin) as Hout'. cbn beta iota in Hout'. clear - Hout' H1 H2. lia.
    + eapply mem_grows_trans; [exact (SGP.i_grows _ _ _ _ _ _ _ _ _ HI) | exact Hgr].
    + eapply SGP.regions_ok_agree; [exact Fvars | exact Hag0 | exact (SGP.i_flat _ _ _ _ _ _ _ _ _ HI)].
    + cbn [SR.after_call s_next]. pose proof (SGP.i_nx _ _ _ _ _ _ _ _ _ HI). lia.
    + eapply SGP.bfacts_agree; [exact BRvars | exact Hag0 | exact (SGP.i_bf _ _ _ _ _ _ _ _ _ HI)].
  - cbn [SR.after_call s_pc]. rewrite Hpc. exact Hms.
Qed.

End WithImage.

(* [comment removed for export] *)
Definition xstep (segs : list Segment) (MSET MCPY : Z) (CELLS : list (Z * nat * Z)) (TLSPC : Z) (TCELLS : list (Z * nat * Z)) (TPV ENTV CTXSLOT BLKSLOT : Z)
    (F : list SGP.region) (id : nat) (ss : sym_state) : option sym_state :=
  match id with
  | 0%nat => xmemset MSET CELLS F ss
  | 1%nat => xmemcpy segs MCPY CELLS F ss
  | 2%nat => xtls TLSPC TCELLS TPV ENTV CTXSLOT BLKSLOT F ss
  | _ => None
  end.
Theorem xstep_ok : forall segs MSET MCPY CELLS TLSPC TCELLS TPV ENTV CTXSLOT BLKSLOT,
  icpt_fill_spec segs MSET CELLS -> icpt_copy_spec segs MCPY CELLS -> icpt_tls_spec segs TLSPC TCELLS TPV ENTV CTXSLOT BLKSLOT ->
  forall nx0 BR F M0, SGP.XSTEP_ok segs nx0 BR (xstep segs MSET MCPY CELLS TLSPC TCELLS TPV ENTV CTXSLOT BLKSLOT) F M0.
Proof.
  intros segs MSET MCPY CELLS TLSPC TCELLS TPV ENTV CTXSLOT BLKSLOT HF HC HT nx0 BR F M0 Fvars BRvars fx id ss ss' E R Mc H HI.
  destruct id as [|[|[|id]]]; [| | |discriminate H].
  - exact (xmemset_ok segs MSET CELLS HF nx0 BR F M0 fx ss ss' E R Mc Fvars BRvars H HI).
  - exact (xmemcpy_ok segs MCPY CELLS HC nx0 BR F M0 fx ss ss' E R Mc Fvars BRvars H HI).
  - exact (xtls_ok segs TLSPC TCELLS TPV ENTV CTXSLOT BLKSLOT HT nx0 BR F M0 fx ss ss' E R Mc Fvars BRvars H HI).
Qed.

(* [comment removed for export] *)
Definition AS0_MSET : Z := 0x77c88.
Definition AS0_MCPY : Z := 0x77c90.
Definition AS0_CELLS : list (Z * nat * Z) :=
  [ (0x1374c0, 8%nat, 0x13fc38); (0x13fc38, 8%nat, SB);            (* [comment removed for export] *)
    (0x1374c8, 8%nat, 0x140928); (0x140928, 8%nat, 0);             (* [comment removed for export] *)
    (0x1374d0, 8%nat, 0x140930); (0x140930, 8%nat, 0);             (* [comment removed for export] *)
    (0x1374d8, 8%nat, 0x140920); (0x140920, 8%nat, HIGHEND);       (* [comment removed for export] *)
    (0x138028, 8%nat, 0x140919); (0x140919, 1%nat, 1);             (* [comment removed for export] *)
    (0x1394d0, 8%nat, 0x129d04);                                  (* [comment removed for export] *)
    (0x1394c8, 8%nat, 0x129900) ].                                (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AS0_TLSPC : Z := 0x633f0.
Definition AS0_TPV : Z := 0x673d00.
Definition AS0_ENTV : Z := 0x674500.
Definition AS0_CTXSLOT : Z := 0x6951b8.
Definition AS0_BLKSLOT : Z := 0x673d08.
Definition AS0_TCELLS : list (Z * nat * Z) :=
  [ (0x140918, 1%nat, 1); (0x1393c0, 8%nat, 0x12a8e4);
    (0x673cf8, 8%nat, 0x673d20); (0x673d28, 8%nat, 0x674500);
    (0x13f4a0, 1%nat, 1); (0x13f4a4, 4%nat, 0); (0x673ca8, 8%nat, 0x6951b8);
    (0x1374b0, 8%nat, 0x1d1768); (0x1d17f1, 1%nat, 1);
    (0x137510, 8%nat, 0x1cf6d8); (0x1cf6d8, 4%nat, 0);
    (0x1382c8, 8%nat, 8) ].
End XIA.
