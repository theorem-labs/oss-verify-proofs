(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.





Section WithTables.
Variable segs : list Segment.
Variable IT : itab.
Variable nx0 : nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint kimg_cover (k : list kentry) (lo hi : Z) : bool :=
  match k with
  | [] => false
  | KImg l h :: rest => (Z.leb l lo && Z.leb hi h) || kimg_cover rest lo hi
  | _ :: rest => kimg_cover rest lo hi
  end%bool.

(* [comment removed for export] *)
Definition rom_load (sz : msize) (sx : bool) (j : Z) : option Z :=
  match rdn segs (fun _ => None) (Z_to_bv 64 j) (AzSymStepR.msize_bytes sz) with
  | Some bs => Some (bv_unsigned (load_result sz sx bs))
  | None => None
  end.

Definition node_enumload_stride (cs : acs) : option acs :=
  match itab_lookup IT (pc cs) with
  | Some (Load sz sx rd rs imm) =>
      let n := Z.of_nat (AzSymStepR.msize_bytes sz) in
      let a := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm) in
      match xlo (kn cs) a, xhi (kn cs) a with
      | Some lo, Some hi =>
          (* [comment removed for export] *)
          let g := 2 ^ Z.min (ealign (kn cs) a) 12 in
          let lo' := (lo + g - 1) / g * g in
          if (fresh_ok nx0 cs && kimg_cover (kn cs) lo (hi + n) && Z.leb 0 lo && Z.leb lo' hi && Z.leb ((hi - lo') / g) ENUM_MAX
              && Z.ltb (hi + n) two64 && negb (bv_eqb rd 0%bv)
              && Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool
          then match enum_minmax (fun i => rom_load sz sx (lo' + g * i)) 0 ((hi - lo') / g) with
               | Some (mn, mx) =>
                   let v := nxt cs in
                   let ss := a_ss cs in
                   Some (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs ss) (ridx rd) (EVar v))
                                           (KRange (EVar v) mn mx :: s_know ss) (S v)))
               | None => None
               end
          else None
      | _, _ => None
      end
  | Some _ => Some cs      (* [comment removed for export] *)
  | None => Some cs        (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition lin1 (e : expr) : option (Z * Z * expr) :=
  match lin_of e with
  | (c, [(k, x)]) => Some (c, k, x)
  | _ => None
  end.
Definition cand_load (k : list kentry) (sz : msize) (sx : bool) (n : Z) (adr : Z) : option Z :=
  if (kimg_cover k adr (adr + n) && Z.leb 0 adr && Z.ltb (adr + n) two64)%bool then rom_load sz sx adr else None.
Definition node_enumlin (cs : acs) : option acs :=
  match itab_lookup IT (pc cs) with
  | Some (Load sz sx rd rs imm) =>
      let n := Z.of_nat (AzSymStepR.msize_bytes sz) in
      let a := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm) in
      match lin1 a with
      | None => None
      | Some (c0, kk, x) =>
          match xlo (kn cs) x, xhi (kn cs) x with
          | Some elo, Some ehi =>
              if (fresh_ok nx0 cs && Z.leb 0 elo && Z.leb elo ehi && Z.leb (ehi - elo) ENUM_MAX && negb (bv_eqb rd 0%bv)
                  && Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool
              then match enum_minmax (fun i => cand_load (kn cs) sz sx n ((c0 + kk * (elo + i)) mod two64)) 0 (ehi - elo) with
                   | Some (mn, mx) =>
                       let v := nxt cs in
                       let ss := a_ss cs in
                       Some (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs ss) (ridx rd) (EVar v))
                                               (KRange (EVar v) mn mx :: s_know ss) (S v)))
                   | None => None
                   end
              else None
          | _, _ => None
          end
      end
  | _ => None
  end.
Definition node_enumload (cs : acs) : option acs :=
  match node_enumlin cs with Some cs' => Some cs' | None => node_enumload_stride cs end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition node_havoc64 (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit r] =>
      if (Z.leb 1 r && Z.leb r 31 && fresh_ok nx0 cs && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool then
        let v := nxt cs in
        let ss := a_ss cs in
        Some (with_ss cs (mk_ss (s_pc ss) (sr_upd (s_regs ss) (Z.to_nat r) (EVar v))
                                (KRange (EVar v) 0 (two64 - 1) :: s_know ss) (S v)))
      else None
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition popcnt_chain_ref (fk : list kentry) (x : expr) : expr :=
  let a6 := mkAluK fk ALU_SRL x (ELit 1) in
  let a6 := mkAluK fk ALU_AND a6 (ELit M55) in
  let a5 := mkAluK fk ALU_AND x (ELit (-2)) in
  let a5 := mkAluK fk ALU_SUB a5 a6 in
  let a6 := mkAluK fk ALU_AND a5 (ELit M33) in
  let a5 := mkAluK fk ALU_SRL a5 (ELit 2) in
  let a5 := mkAluK fk ALU_AND a5 (ELit M33) in
  let a5 := mkAluK fk ALU_ADD a6 a5 in
  let a6 := mkAluK fk ALU_SRL a5 (ELit 4) in
  let a5 := mkAluK fk ALU_ADD a5 a6 in
  let a5 := mkAluK fk ALU_AND a5 (ELit M0f) in
  let a5 := mkMdK fk M_MUL a5 (ELit M01) in
  mkAluK fk ALU_SRL a5 (ELit 56).
(* [comment removed for export] *)
Definition popcnt_chainB (bc : AX2B.bctx) (x : expr) : expr :=
  let a6 := AX2B.mkAluKB bc ALU_SRL x (ELit 1) in
  let a6 := AX2B.mkAluKB bc ALU_AND a6 (ELit M55) in
  let a5 := AX2B.mkAluKB bc ALU_AND x (ELit (-2)) in
  let a5 := AX2B.mkAluKB bc ALU_SUB a5 a6 in
  let a6 := AX2B.mkAluKB bc ALU_AND a5 (ELit M33) in
  let a5 := AX2B.mkAluKB bc ALU_SRL a5 (ELit 2) in
  let a5 := AX2B.mkAluKB bc ALU_AND a5 (ELit M33) in
  let a5 := AX2B.mkAluKB bc ALU_ADD a6 a5 in
  let a6 := AX2B.mkAluKB bc ALU_SRL a5 (ELit 4) in
  let a5 := AX2B.mkAluKB bc ALU_ADD a5 a6 in
  let a5 := AX2B.mkAluKB bc ALU_AND a5 (ELit M0f) in
  let a5 := AX2B.mkMdKB bc M_MUL a5 (ELit M01) in
  AX2B.mkAluKB bc ALU_SRL a5 (ELit 56).
Definition popcnt_chain (fk : list kentry) (x : expr) : expr := popcnt_chainB (AX2B.mkbc fk) x.
Lemma popcnt_chain_eq : forall fk x, popcnt_chain fk x = popcnt_chain_ref fk x.
Proof. intros. unfold popcnt_chain, popcnt_chainB, popcnt_chain_ref. rewrite !AX2B.mkAluKB_eqf, !AX2B.mkMdKB_eqf. reflexivity. Qed.

Definition node_popcnt (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit r] =>
      if (Z.leb 1 r && Z.leb r 31)%bool then
        let x := nth (Z.to_nat r) (s_regs (a_ss cs)) (ELit 0) in
        Some (add_kn cs [KRange (popcnt_chain (facts_of (kn cs)) x) 0 64])
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_enumreg (args : list expr) (cs : acs) : option acs :=
  match args with
  | [ELit r; s] => if (Z.leb 0 r && Z.leb r 31)%bool then node_enumrange [nth (Z.to_nat r) (s_regs (a_ss cs)) (ELit 0); s] cs else None
  | _ => None
  end.

End WithTables.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kimg_cover_sound : forall segs E M k lo hi,
  know_ok segs E M k -> kimg_cover k lo hi = true -> forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
Proof.
  intros segs E M k lo hi Hk. induction k as [|K rest IH]; intros Hc i Hi; [discriminate|].
  apply Forall_cons_iff in Hk as [HK Hrest]. cbn [kimg_cover] in Hc.
  destruct K; try exact (IH Hrest Hc i Hi).
  apply orb_prop in Hc as [Hc|Hc]; [|exact (IH Hrest Hc i Hi)].
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [kentry_ok] in HK. destruct HK as (_ & _ & HK). apply HK. lia.
Qed.

Lemma rdn_overlay_none : forall segs M n (a : word),
  (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (bv_unsigned a + i)) = None) ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  rdn segs M a n = rdn segs (fun _ => None) a n.
Proof.
  intros segs M n. induction n as [|n IH]; intros a HM Hn; [reflexivity|].
  cbn [rdn]. pose proof (u64_range a) as Ha.
  assert (H0 : M a = None).
  { specialize (HM 0 ltac:(lia)). rewrite Z.add_0_r, Z_to_bv_bv_unsigned in HM. exact HM. }
  rewrite H0.
  destruct (seg_rom segs a) as [b|]; [|reflexivity].
  destruct n as [|n']; [reflexivity|].
  rewrite (IH (a + 1)%bv); [reflexivity| |].
  - intros i Hi. rewrite u_add1 by lia. replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia.
    apply HM. lia.
  - rewrite u_add1 by lia. lia.
Qed.

Lemma popcnt_chain_val : forall segs E M fk x,
  know_ok segs E M fk ->
  bv_unsigned (edenot E (popcnt_chain fk x)) = swar_popc (bv_unsigned (edenot E x)).
Proof.
  intros segs E M fk x Hk. rewrite popcnt_chain_eq. unfold popcnt_chain_ref, swar_popc. cbv zeta.
  repeat ((rewrite (mkAluK_denot segs E M fk) by exact Hk) || (rewrite (mkMdK_denot segs E M fk) by exact Hk)).
  repeat (rewrite u_srl64 || rewrite u_mul64 || rewrite u_and64 || rewrite u_add64 || rewrite u_sub64).
  cbn [edenot]. rewrite !u_lit64.
  change ((1 mod two64) mod 64) with 1. change ((2 mod two64) mod 64) with 2. change ((4 mod two64) mod 64) with 4.
  change ((56 mod two64) mod 64) with 56.
  change (M55 mod two64) with M55. change (M33 mod two64) with M33. change (M0f mod two64) with M0f. change (M01 mod two64) with M01.
  change ((-2) mod two64) with MFE.
  rewrite !Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable SHC : list (Z * Z).      (* [comment removed for export] *)
Variable VSH : list (Z * Z).      (* [comment removed for export] *)
Variable AINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> (word -> option byte) -> Model -> Prop.   (* [comment removed for export] *)
Variable KCAP : Z.
Variable FTOPc : Z.   (* [comment removed for export] *)
Hypothesis AINV_frame : forall Lc Lf B C K M M' mdl,
  AINV Lc Lf B C K M mdl -> (forall a, M' a <> M a -> gowned SWIN PERMc SPTOPc SB Lc Lf a /\ M' a <> None) ->
  AINV Lc Lf B C K M' mdl.
Hypothesis AINV_lazy : forall Lc Lf B C K M mdl,
  AINV Lc Lf B C K M mdl ->
  exists AA, A_wf AA /\ MInv AA mdl
    /\ (forall a : word, GPS.in_shc SHC (bv_unsigned a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall a : word, GPS.in_shv VSH (bv_unsigned a) = true -> page_allowedb AA (page_base a) = true)
    /\ (forall (a : word) b n, In (b, n) (Lc ++ Lf) -> in_shadow SB b n (bv_unsigned a) -> page_allowedb AA (page_base a) = true)
    /\ (forall mdl', MInv AA mdl' -> same_but_materialized mdl mdl' -> AINV Lc Lf B C K M mdl').
Variable A : atable.
Hypothesis AINV_facts : forall Lc Lf B C K M mdl,
  AINV Lc Lf B C K M mdl ->
  Forall (fun iv => 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL_run
                    /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))) (m_vm_lazy mdl).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_silent1 : GPS.RZ_SILENT1 SEGS RZ.
Hypothesis RZ_exit : GPS.RZ_EXIT SEGS RZ.
Hypothesis RZ_conseq : GPS.RZ_CONSEQ RZ.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ).

Theorem node_popcnt_sound : forall args, node1_stmt always (node_popcnt args).
Proof.
  intros args. apply (add_facts_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV). intros cs cs' E fx R M model HC Hn.
  unfold node_popcnt in Hn. destruct args as [|[r| | | | | | |] [|]]; try discriminate.
  destruct ((1 <=? r) && (r <=? 31))%bool; [|discriminate]. injection Hn as <-.
  eexists. split; [reflexivity|]. constructor; [|constructor].
  cbn [kentry_ok]. rewrite (popcnt_chain_val SEGS E _ (facts_of (kn cs))) by (apply facts_of_ok; exact (co_know HC)).
  apply swar_popc_bound. apply u64_range.
Qed.

Theorem node_enumload_stride_sound : node1_stmt always (node_enumload_stride SEGS IT nx0).
Proof.
  intros cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_enumload_stride in Hn.
  destruct (itab_lookup IT (pc cs)) as [i|] eqn:Hit.
  2:{ injection Hn as <-. apply (Hk E fx R M model); [split; apply env_agree_refl | exact HC | reflexivity]. }
  destruct i as [| | | | |sz sx rd rs imm| | | | | | | | | | | | | | | | | | | | | | | | | | | | |];
    try (injection Hn as <-; apply (Hk E fx R M model); [split; apply env_agree_refl | exact HC | reflexivity]).
  set (ae := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm)) in Hn.
  destruct (xlo (kn cs) ae) as [lo|] eqn:Hxlo; [|discriminate].
  destruct (xhi (kn cs) ae) as [hi|] eqn:Hxhi; [|discriminate].
  cbv zeta in Hn.
  set (g := 2 ^ Z.min (ealign (kn cs) ae) 12) in Hn.
  set (lo' := (lo + g - 1) / g * g) in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (enum_minmax (fun i => rom_load SEGS sz sx (lo' + g * i)) 0 ((hi - lo') / g)) as [[mn mx]|] eqn:Hen; [|discriminate].
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hc Hpc4]. apply andb_prop in Hc as [Hc Hpc0].
  apply andb_prop in Hc as [Hc Hrd]. apply andb_prop in Hc as [Hc Hhi64]. apply andb_prop in Hc as [Hc Hmax].
  apply andb_prop in Hc as [Hc Hlohi]. apply andb_prop in Hc as [Hc Hlo0]. apply andb_prop in Hc as [Hfresh Hcov].
  apply Z.leb_le in Hlo0. apply Z.leb_le in Hlohi. apply Z.ltb_lt in Hhi64. apply Z.leb_le in Hpc0. apply Z.ltb_lt in Hpc4.
  apply Z.leb_le in Hmax.
  apply negb_true_iff in Hrd. apply Nat.eqb_eq in Hlen. unfold two64 in Hhi64, Hpc4.
  pose proof (IT_ok _ _ Hit) as Hen2. unfold itab_entry in Hen2.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' isz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb isz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz.
  injection Hen2 as ->.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs HC) as HR.
  pose proof (co_know HC) as HK.
  set (H := GPS.hid SHC VSH E cs model).
  set (MR := GPS.Mr SHC VSH E cs model M) in *.
  assert (Haddr : v_addi (getr R rs) (bv_signed imm) = edenot E ae).
  { unfold ae, eaddz. rewrite mkAlu_denot. rewrite (HR rs). cbn [edenot]. rewrite alu_add. unfold v_addi, v_add.
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. }
  pose proof (xlo_sound SEGS E MR (kn cs) ae lo HK Hxlo) as Blo.
  pose proof (xhi_sound SEGS E MR (kn cs) ae hi HK Hxhi) as Bhi.
  (* [comment removed for export] *)
  pose proof (kimg_cover_sound SEGS E MR (kn cs) lo _ HK Hcov) as Himg.
  (* [comment removed for export] *)
  assert (Hg : 0 < g).
  { subst g. apply Z.pow_pos_nonneg; [lia|]. pose proof (ealign_sound SEGS E MR (kn cs) ae HK) as [Hr _]. lia. }
  assert (Hdiv : (g | bv_unsigned (edenot E ae))).
  { pose proof (ealign_sound SEGS E MR (kn cs) ae HK) as [Hr Hdv]. subst g.
    destruct Hdv as [q Hq]. exists (q * 2 ^ (ealign (kn cs) ae - Z.min (ealign (kn cs) ae) 12)). rewrite Hq at 1.
    rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia. }
  set (u := bv_unsigned (edenot E ae)) in *.
  assert (Hlo'g : (g | lo')) by (exists ((lo + g - 1) / g); subst lo'; lia).
  assert (Hlo'le : lo' <= u).
  { subst lo'. destruct Hdiv as [q Hq].
    assert (Hlt : (lo + g - 1) / g < q + 1) by (apply Z.div_lt_upper_bound; [lia|nia]).
    assert (Hq' : (lo + g - 1) / g * g <= q * g); [|lia].
    apply Z.mul_le_mono_nonneg_r; lia. }
  set (j := (u - lo') / g).
  assert (Hj : u = lo' + g * j).
  { subst j. destruct Hdiv as [q Hq]. destruct Hlo'g as [q' Hq']. rewrite Hq, Hq'.
    replace (q * g - q' * g) with ((q - q') * g) by lia. rewrite Z.div_mul by lia. lia. }
  destruct (enum_minmax_spec _ _ _ _ _ Hen j) as (val & Hval & Hb).
  { subst j. split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]. }
  cbv beta in Hval. rewrite <- Hj in Hval.
  unfold rom_load in Hval. subst u. rewrite Z_to_bv_bv_unsigned in Hval.
  destruct (rdn SEGS (fun _ => None) (edenot E ae) (AzSymStepR.msize_bytes sz)) as [bs|] eqn:Hrdn0; [|discriminate].
  injection Hval as <-.
  assert (Hrdn : rdn SEGS MR (edenot E ae) (AzSymStepR.msize_bytes sz) = Some bs).
  { rewrite rdn_overlay_none; [exact Hrdn0 | | lia]. intros i Hi. apply Himg. lia. }
  pose proof (rdn_length _ _ _ _ _ Hrdn) as Hbslen.
  set (val := load_result sz sx bs) in *.
  set (v := nxt cs) in *.
  set (E' := ext1 E v val).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  set (R' := regupd R rd val).
  (* [comment removed for export] *)
  assert (Hstep : RiscvSemantics.step SEGS (restrict H (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS)))
                  = MachineOk (mkstF fx R' (Z_to_bv 64 (pc cs + 4)) MR (seg_rom SEGS))).
  { change (restrict H (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))) with (mkstF fx R (Z_to_bv 64 (pc cs)) MR (seg_rom SEGS)).
    unfold mkstF. rewrite <- !mkstR_None.
    rewrite (stepR_load fx SEGS R _ MR (seg_rom SEGS) None w sz sx rd rs imm bs Hf Hec Hd).
    - rewrite Hrd. rewrite v_addi_pc4 by assumption. reflexivity.
    - rewrite Haddr. exact Hrdn. }
  eapply (GPS.restricted_run_sound SEGS A PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc AINV_lazy AINV_facts FXOK UINV RZ RZ_silent1 SEGS_in_hull SEGS_wx);
    [exact HC | eapply msteps_one; [reflexivity | exact Hstep] |].
  intros model' Hsame Hhid Hhalt' Hfs' Hfds' HA' Hclean.
  unfold unrestrict. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom mkstF mkst].
  unfold MR, GPS.Mr. fold H. rewrite munrestrict_mrestrict.
  pose proof (cs_ok_agree SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
  specialize (Hk E' fx R' M model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc. apply Hk; [|exact Hfs'].
  eapply (cs_ok_frame_mat SEGS SWIN PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc AINV_frame FXOK UINV);
    [exact HC' | | reflexivity | | exact (co_fx HC) | | exact Hsame |].
  - (* [comment removed for export] *) cbn [mk_ss s_regs].
    pose proof (regs_ok_agree' (nxt cs) E E' _ R Hag Fsr HR) as HR1.
    pose proof (regs_ok_upd E' (s_regs (a_ss cs)) R rd val (EVar v) HR1) as HR2.
    rewrite Hrd in HR2. apply HR2. cbn [edenot]. unfold E'. apply ext1_at.
  - (* [comment removed for export] *) cbn [mk_ss s_know]. rewrite (GPS.Mr_agreeE nx0 SHC VSH E E' cs model' M Hag Hfresh).
    unfold GPS.Mr. rewrite Hhid. fold H. change (mrestrict H M) with MR. constructor.
    + cbn [kentry_ok edenot]. unfold E'. rewrite ext1_at. exact Hb.
    + eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK].
  - (* [comment removed for export] *) intros a Ha. exfalso. apply Ha. reflexivity.
  - destruct (GPS.fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt].
    rewrite (GPS.blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (GPS.pairs_vars_lt_app_l _ _ _ Fallow)).
    rewrite (GPS.blocks_den_agree (nxt cs) E E' (a_fake cs) Hag Ffk).
    rewrite (GPS.bcost_agree (nxt cs) E E' (a_vis cs) Hag (GPS.pairs_vars_lt_app_l _ _ _ Fallow)).
    rewrite (GPS.uE_agree (nxt cs) E E' (a_meter cs) Hag Fmt). exact HA'.
Qed.

Theorem node_enumlin_sound : node1_stmt always (node_enumlin SEGS IT nx0).
Proof.
  intros cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_enumlin in Hn.
  destruct (itab_lookup IT (pc cs)) as [i|] eqn:Hit; [|discriminate].
  destruct i as [| | | | |sz sx rd rs imm| | | | | | | | | | | | | | | | | | | | | | | | | | | | |]; try discriminate.
  set (ae := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm)) in Hn.
  destruct (lin1 ae) as [[[c0 kk] x]|] eqn:Hlin; [|discriminate].
  destruct (xlo (kn cs) x) as [elo|] eqn:Hxlo; [|discriminate].
  destruct (xhi (kn cs) x) as [ehi|] eqn:Hxhi; [|discriminate].
  cbv zeta in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  set (nb := Z.of_nat (AzSymStepR.msize_bytes sz)) in Hn.
  destruct (enum_minmax (fun i => cand_load SEGS (kn cs) sz sx nb ((c0 + kk * (elo + i)) mod two64)) 0 (ehi - elo)) as [[mn mx]|] eqn:Hen; [|discriminate].
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hc Hpc4]. apply andb_prop in Hc as [Hc Hpc0].
  apply andb_prop in Hc as [Hc Hrd]. apply andb_prop in Hc as [Hc Hmax]. apply andb_prop in Hc as [Hc Hlohi].
  apply andb_prop in Hc as [Hfresh Hlo0].
  apply Z.leb_le in Hlo0. apply Z.leb_le in Hlohi. apply Z.leb_le in Hpc0. apply Z.ltb_lt in Hpc4. apply Z.leb_le in Hmax.
  apply negb_true_iff in Hrd. apply Nat.eqb_eq in Hlen. unfold two64 in Hpc4.
  pose proof (IT_ok _ _ Hit) as Hen2. unfold itab_entry in Hen2.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' isz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb isz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz.
  injection Hen2 as ->.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs HC) as HR.
  pose proof (co_know HC) as HK.
  set (H := GPS.hid SHC VSH E cs model).
  set (MR := GPS.Mr SHC VSH E cs model M) in *.
  assert (Haddr : v_addi (getr R rs) (bv_signed imm) = edenot E ae).
  { unfold ae, eaddz. rewrite mkAlu_denot. rewrite (HR rs). cbn [edenot]. rewrite alu_add. unfold v_addi, v_add.
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. }
  (* [comment removed for export] *)
  set (u := bv_unsigned (edenot E ae)) in *.
  pose proof (xlo_sound SEGS E MR (kn cs) x elo HK Hxlo) as Bxlo.
  pose proof (xhi_sound SEGS E MR (kn cs) x ehi HK Hxhi) as Bxhi.
  assert (Hu : u = (c0 + kk * bv_unsigned (edenot E x)) mod two64).
  { pose proof (lin_of_sound E ae) as [q Hq]. unfold lin1 in Hlin.
    destruct (lin_of ae) as [c ts] eqn:Hlo. destruct ts as [|[k1 x1] [|]]; try discriminate.
    injection Hlin as -> -> ->. unfold lden, tden, AX2S.uE in Hq. cbn [fst snd] in Hq.
    pose proof (u64_range (edenot E ae)) as Hur. subst u. unfold two64.
    replace (c0 + kk * bv_unsigned (edenot E x)) with (bv_unsigned (edenot E ae) + q * 2 ^ 64) by (cbn [fst snd] in Hq; lia).
    rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
  set (j := bv_unsigned (edenot E x) - elo).
  destruct (enum_minmax_spec _ _ _ _ _ Hen j) as (val & Hval & Hb); [subst j; lia|].
  cbv beta in Hval. replace (elo + j) with (bv_unsigned (edenot E x)) in Hval by (subst j; lia).
  rewrite <- Hu in Hval. unfold cand_load in Hval.
  match type of Hval with (if ?c then _ else _) = _ => destruct c eqn:Hcc; [|discriminate] end.
  apply andb_prop in Hcc as [Hcc Hhi64]. apply andb_prop in Hcc as [Hcov Hu0]. apply Z.ltb_lt in Hhi64. unfold two64 in Hhi64.
  pose proof (kimg_cover_sound SEGS E MR (kn cs) u _ HK Hcov) as Himg.
  unfold rom_load in Hval. subst u. rewrite Z_to_bv_bv_unsigned in Hval.
  destruct (rdn SEGS (fun _ => None) (edenot E ae) (AzSymStepR.msize_bytes sz)) as [bs|] eqn:Hrdn0; [|discriminate].
  injection Hval as <-.
  assert (Hrdn : rdn SEGS MR (edenot E ae) (AzSymStepR.msize_bytes sz) = Some bs).
  { rewrite rdn_overlay_none; [exact Hrdn0 | | subst nb; lia]. intros i0 Hi0. apply Himg. subst nb. lia. }
  pose proof (rdn_length _ _ _ _ _ Hrdn) as Hbslen.
  set (val := load_result sz sx bs) in *.
  set (v := nxt cs) in *.
  set (E' := ext1 E v val).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  set (R' := regupd R rd val).
  (* [comment removed for export] *)
  assert (Hstep : RiscvSemantics.step SEGS (restrict H (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS)))
                  = MachineOk (mkstF fx R' (Z_to_bv 64 (pc cs + 4)) MR (seg_rom SEGS))).
  { change (restrict H (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))) with (mkstF fx R (Z_to_bv 64 (pc cs)) MR (seg_rom SEGS)).
    unfold mkstF. rewrite <- !mkstR_None.
    rewrite (stepR_load fx SEGS R _ MR (seg_rom SEGS) None w sz sx rd rs imm bs Hf Hec Hd).
    - rewrite Hrd. rewrite v_addi_pc4 by assumption. reflexivity.
    - rewrite Haddr. exact Hrdn. }
  eapply (GPS.restricted_run_sound SEGS A PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc AINV_lazy AINV_facts FXOK UINV RZ RZ_silent1 SEGS_in_hull SEGS_wx);
    [exact HC | eapply msteps_one; [reflexivity | exact Hstep] |].
  intros model' Hsame Hhid Hhalt' Hfs' Hfds' HA' Hclean.
  unfold unrestrict. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom mkstF mkst].
  unfold MR, GPS.Mr. fold H. rewrite munrestrict_mrestrict.
  pose proof (cs_ok_agree SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
  specialize (Hk E' fx R' M model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc. apply Hk; [|exact Hfs'].
  eapply (cs_ok_frame_mat SEGS SWIN PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc AINV_frame FXOK UINV);
    [exact HC' | | reflexivity | | exact (co_fx HC) | | exact Hsame |].
  - (* [comment removed for export] *) cbn [mk_ss s_regs].
    pose proof (regs_ok_agree' (nxt cs) E E' _ R Hag Fsr HR) as HR1.
    pose proof (regs_ok_upd E' (s_regs (a_ss cs)) R rd val (EVar v) HR1) as HR2.
    rewrite Hrd in HR2. apply HR2. cbn [edenot]. unfold E'. apply ext1_at.
  - (* [comment removed for export] *) cbn [mk_ss s_know]. rewrite (GPS.Mr_agreeE nx0 SHC VSH E E' cs model' M Hag Hfresh).
    unfold GPS.Mr. rewrite Hhid. fold H. change (mrestrict H M) with MR. constructor.
    + cbn [kentry_ok edenot]. unfold E'. rewrite ext1_at. exact Hb.
    + eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK].
  - (* [comment removed for export] *) intros a Ha. exfalso. apply Ha. reflexivity.
  - destruct (GPS.fresh_ok_parts2 nx0 cs Hfresh) as [Ffk Fmt].
    rewrite (GPS.blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (GPS.pairs_vars_lt_app_l _ _ _ Fallow)).
    rewrite (GPS.blocks_den_agree (nxt cs) E E' (a_fake cs) Hag Ffk).
    rewrite (GPS.bcost_agree (nxt cs) E E' (a_vis cs) Hag (GPS.pairs_vars_lt_app_l _ _ _ Fallow)).
    rewrite (GPS.uE_agree (nxt cs) E E' (a_meter cs) Hag Fmt). exact HA'.
Qed.

Theorem node_enumload_sound : node1_stmt always (node_enumload SEGS IT nx0).
Proof.
  intros cs cs' E fx R M model T HC HT Hn Hk. unfold node_enumload in Hn.
  destruct (node_enumlin SEGS IT nx0 cs) as [cs1|] eqn:H1.
  - injection Hn as <-. exact (node_enumlin_sound cs cs1 E fx R M model T HC HT H1 Hk).
  - exact (node_enumload_stride_sound cs cs' E fx R M model T HC HT Hn Hk).
Qed.

Theorem node_enumreg_sound : forall args, node1_stmt always (node_enumreg args).
Proof.
  intros args cs cs' E fx R M model T HC Hp Hn Hk. unfold node_enumreg in Hn.
  destruct args as [|[r| | | | | | |] [|s [|]]]; try discriminate.
  destruct (Z.leb 0 r && Z.leb r 31)%bool; [|discriminate].
  exact (node_enumrange_sound SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV RZ _ cs cs' E fx R M model T HC Hp Hn Hk).
Qed.

Theorem node_havoc64_sound : forall args, node1_stmt always (node_havoc64 nx0 args).
Proof.
  intros args cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_havoc64 in Hn. destruct args as [|[r| | | | | | |] [|]]; try discriminate.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hr1 Hr31].
  apply Z.leb_le in Hr1. apply Z.leb_le in Hr31. apply Nat.eqb_eq in Hlen.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs HC) as HR. pose proof (co_know HC) as HK.
  set (v := nxt cs) in *.
  set (rd := (Z_to_bv 5 r : bv 5)).
  assert (Hrd : ridx rd = Z.to_nat r).
  { unfold ridx, rd. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.iter Z.mul].
    rewrite Z.mod_small by lia. reflexivity. }
  set (val := getr R rd).
  set (E' := ext1 E v val).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  pose proof (cs_ok_agree SEGS nx0 PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
  specialize (Hk E' fx R M model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc. apply Hk; [|reflexivity].
  eapply (cs_ok_frame SEGS SWIN PERMc SPTOPc FS0 SHC VSH AINV KCAP FTOPc AINV_frame FXOK UINV); [exact HC' | | reflexivity | | exact (co_fx HC) |].
  - (* [comment removed for export] *) cbn [mk_ss s_regs].
    pose proof (regs_ok_agree' (nxt cs) E E' _ R Hag Fsr HR) as HR1.
    rewrite <- Hrd. apply regs_ok_pin; [exact HR1|]. cbn [edenot]. unfold E'. rewrite ext1_at. reflexivity.
  - (* [comment removed for export] *) cbn [mk_ss s_know]. rewrite (GPS.Mr_agreeE nx0 SHC VSH E E' cs model M Hag Hfresh). constructor.
    + cbn [kentry_ok edenot]. pose proof (u64_range (ev E' v)). unfold two64. lia.
    + eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK].
  - (* [comment removed for export] *) intros a Ha. exfalso. apply Ha. reflexivity.
Qed.

End Sound.
