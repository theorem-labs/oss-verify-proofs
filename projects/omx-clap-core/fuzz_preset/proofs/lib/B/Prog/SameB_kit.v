(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B' (asan-ubsan #102 pin d663f82d7f48, unstripped twin c90d4fa54d43), the walk of
   same (fuzz_preset.c:65-86): the GENERIC kit of the walk - no image fact, no address. Ported from the image-A walk of
   same (h-hpreset-7's slice S9, origin/cold/h-hpreset-7-walk-s9-got-rob 9a0674f0b5f2): lib/A/Prog/Wsame_kit.v (hand
   loads, the journal through a materializing step, a state re-expressed in another valuation), Wsame_pj.v (the tree
   facts PRH_Reader.v's frame section does not state), Wsame_base.v (shadow arithmetic) and the journal-generic parts of
   S911Kit.v (the entry facts of afn_pre_x, the frame-below keep, the alloc.c ledger keep and the branch tactic), with
   the s9_ / s911_ names renamed smb_ / smbk_. Two changes, both forced by the #102 kit decff67d721f: the ledger keep
   states prh_ledger at image B's PrhImg prh_img_B with #102's two cells (most own, PRH_Base.v prh_glob: g_most and
   g_own_ran_out), and it reads those two cells' bounds from the generated table like the other five.
   Numerals: 8 / 64 (LENGTH: shadow granule / shadow word), 56 (LENGTH: struct pj), 2 ^ 46 / 2 ^ 47 / 4 (DERIVED: the stack
   atom's range and alignment, astk_ok), 2 ^ 64 (DERIVED: word). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN01 YK19.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section h. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable tbl : ctable.
Hypothesis TBL : table_ok segs tbl.

Lemma smb_not_ecall : forall w sz sg rd rs imm, decode_any (Z_to_bv 32 w) = Some (Load sz sg rd rs imm, 4) ->
  is_ecall (Z_to_bv 32 w) = false.
Proof.
intros w sz sg rd rs imm Hd. unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|reflexivity].
apply bv_eqb_eq in Eq. rewrite Eq in Hd. vm_compute in Hd. discriminate.
Qed.

Lemma smb_pc4 : forall pc, v_addi (Z_to_bv 64 pc) 4 = (Z_to_bv 64 (pc + 4) : word).
Proof.
intros pc. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* one `ld rd, imm(rs)` from bytes bs at address a: rd takes a fresh atom K holding the loaded word v *)
Lemma smb_hld8 : forall (W : world segs) E ss ms md (rd rs : bv 5) (imm : bv 12) (w a : Z) (bs : list byte) (v : word)
  (K : nat) (Q : world segs -> config -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
  clookup tbl (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4) ->
  bv_eqb rd 0 = false ->
  v_addi (sv_denot E (sr_get (ss_regs ss) rs)) (bv_signed imm) = Z_to_bv 64 a ->
  rdn segs (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 a) 8 = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  (forall ms' mat',
     st_ok segs (havoc E K [v]) (set_regs_pc ss [(rd, SOff K 0)] (ss_pc ss + 4)) (restrict (w_H W) ms') ->
     ms_mem ms' = ms_mem ms ->
     SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
intros W E ss ms md rd rs imm w a bs v K Q HS Hrv Hat Hlk Hdec Hrd Ha Hrdn Hv Hk.
pose proof (st_ok_restrict_mkst segs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (TBL _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false) by exact (smb_not_ecall w _ _ _ _ _ Hdec).
assert (R : getr (ms_regs ms) rs = sv_denot E (sr_get (ss_regs ss) rs)) by exact (st_ok_restrict_reg segs (w_H W) E ss ms rs HS).
rewrite Hshape. eapply (SRr_step segs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. apply (step_ld segs _ _ _ _ _ rd rs imm bs v Hfetch Hec Hdec); [|exact Hv].
  rewrite R, Ha. exact Hrdn.
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
  cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
  apply Hk; [|reflexivity].
  rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS. rewrite smb_pc4.
  apply (st_ok_set_regs segs K E (havoc E K [v]) ss _ _ _ (ss_pc ss + 4) _ [(rd, SOff K 0)] HS (env_agree_havoc E K [v]) Hat Hrv).
  + cbn. rewrite ?Bool.orb_false_r. reflexivity.
  + intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [reflexivity|].
    intros ->. rewrite bv_eqb_refl in Hr. discriminate.
  + constructor; [|constructor]. cbn [fst snd]. split; [exact Hrd|].
    rewrite getr_same by (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate). cbn [sv_denot].
    assert (EK : ew (havoc E K [v]) K = v)
      by (pose proof (ew_havoc_new E K [v] 0 v ltac:(cbn; lia)) as H0; rewrite Nat.add_0_r in H0; exact H0).
    rewrite EK.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* one `lw rd, imm(rs)`: rd takes a fresh atom K holding the sign-extended word v_lw v *)
Lemma smb_hlw : forall (W : world segs) E ss ms md (rd rs : bv 5) (imm : bv 12) (w a : Z) (bs : list byte) (v : word)
  (K : nat) (Q : world segs -> config -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
  clookup tbl (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ4 true rd rs imm, 4) ->
  bv_eqb rd 0 = false ->
  v_addi (sv_denot E (sr_get (ss_regs ss) rs)) (bv_signed imm) = Z_to_bv 64 a ->
  rdn segs (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 a) 4 = Some bs -> bytes_le_to_Z bs = bv_unsigned v ->
  (forall ms' mat',
     st_ok segs (havoc E K [v_lw v]) (set_regs_pc ss [(rd, SOff K 0)] (ss_pc ss + 4)) (restrict (w_H W) ms') ->
     ms_mem ms' = ms_mem ms ->
     SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
intros W E ss ms md rd rs imm w a bs v K Q HS Hrv Hat Hlk Hdec Hrd Ha Hrdn Hv Hk.
pose proof (st_ok_restrict_mkst segs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (TBL _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false) by exact (smb_not_ecall w _ _ _ _ _ Hdec).
assert (R : getr (ms_regs ms) rs = sv_denot E (sr_get (ss_regs ss) rs)) by exact (st_ok_restrict_reg segs (w_H W) E ss ms rs HS).
rewrite Hshape. eapply (SRr_step segs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. apply (step_lw segs _ _ _ _ _ rd rs imm bs v Hfetch Hec Hdec); [|exact Hv].
  rewrite R, Ha. exact Hrdn.
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
  cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
  apply Hk; [|reflexivity].
  rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS. rewrite smb_pc4.
  apply (st_ok_set_regs segs K E (havoc E K [v_lw v]) ss _ _ _ (ss_pc ss + 4) _ [(rd, SOff K 0)] HS (env_agree_havoc E K [v_lw v]) Hat Hrv).
  + cbn. rewrite ?Bool.orb_false_r. reflexivity.
  + intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [reflexivity|].
    intros ->. rewrite bv_eqb_refl in Hr. discriminate.
  + constructor; [|constructor]. cbn [fst snd]. split; [exact Hrd|].
    rewrite getr_same by (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate). cbn [sv_denot].
    assert (EK : ew (havoc E K [v_lw v]) K = v_lw v)
      by (pose proof (ew_havoc_new E K [v_lw v] 0 (v_lw v) ltac:(cbn; lia)) as H0; rewrite Nat.add_0_r in H0; exact H0).
    rewrite EK.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* a symbolic state re-expressed over another valuation E' of the same machine state *)
Lemma smb_st_ok_canon : forall E E' ss ms pc sr rs G,
  st_ok segs E ss ms -> ss_pc ss = pc -> ss_resv ss = None ->
  regs_ok E' sr (ms_regs ms) -> mem_ok segs E' (ms_mem ms) rs -> facts_ok E' G ->
  st_ok segs E' (mkSS pc sr rs None G) ms.
Proof.
intros E E' ss ms pc sr rs G (H1 & H2 & H3 & H4 & H5 & H6 & _ & _ & _) Hpc Hrv Hr Hm Hg.
unfold st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
rewrite Hpc in H2. rewrite Hrv in H4. cbn [resv_denot] in H4. auto 10.
Qed.

(* YFeq.v st_ok_add_atom, copied (YFeq's closure includes cgif-image files) *)
Lemma smb_st_ok_add_atom : forall E ss ms n f, st_ok segs E ss ms -> afact_ok E n f -> st_ok segs E (add_atom ss n f) ms.
Proof.
intros E ss ms n f (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & HG) Hf.
unfold st_ok, add_atom; cbn.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
exact (facts_ok_add_atom E _ n f HG Hf).
Qed.

(* a word chunk of a region from the val_mem fact of its bytes (YN0g.v chunk_ok_cval, re-proved: YN0g's closure is
   cgif's) *)
Lemma smb_chunk_cval : forall E m base off v (val : Z),
  sv_denot E v = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 -> YI04.val_mem segs m (base + off) 8 val ->
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 8 v)).
Proof.
intros E m base off v val Hv Hval H i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (byte_of_word (sv_denot E v) i). split; [reflexivity|].
assert (Hi8 : 0 <= i < 8) by (cbn in Hi; lia).
assert (Hi' : (Z.to_nat i < 8)%nat) by lia.
pose proof (H (Z.to_nat i) Hi') as Hb. rewrite Z2Nat.id in Hb by lia. rewrite Hb.
f_equal. rewrite le_byte_bv by exact Hi'. unfold byte_of_word. rewrite Hv, unsigned_lit_small by lia.
rewrite Z2Nat.id by lia. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma smb_vaddi : forall x i, 0 <= x < 2 ^ 64 -> 0 <= x + i < 2 ^ 64 -> v_addi (Z_to_bv 64 x) i = (Z_to_bv 64 (x + i) : word).
Proof.
intros x i Hx Hxi. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small x) by lia. reflexivity.
Qed.

(* the bytes a val_mem fact names, as the load reads them *)
Lemma smb_rdn_val : forall m a (w : nat) v, YI04.val_mem segs m a w v -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  0 <= v < 2 ^ (8 * Z.of_nat w) ->
  rdn segs m (Z_to_bv 64 a) w = Some (Z_to_le_bytes w v) /\ bytes_le_to_Z (Z_to_le_bytes w v) = v.
Proof.
intros m a w v Hv Ha Haw Hr. split.
- rewrite <- (Z.mod_small v (2 ^ (8 * Z.of_nat w))) by exact Hr. apply bytes_rdn; [exact Ha | exact Haw | exact Hv].
- apply bytes_le_to_Z_Z_to_le_bytes. exact Hr.
Qed.

(* smb_hld8 / smb_hlw with the loaded word named by a val_mem fact *)
Lemma smb_hld8v : forall (W : world segs) E ss ms md (rd rs : bv 5) (imm : bv 12) (w base v : Z) (K : nat)
  (Q : world segs -> config -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
  clookup tbl (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4) ->
  bv_eqb rd 0 = false ->
  sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 base -> 0 <= base < 2 ^ 64 ->
  0 <= base + bv_signed imm -> base + bv_signed imm + 8 <= 2 ^ 64 ->
  YI04.val_mem segs (mrestrict (w_H W) (ms_mem ms)) (base + bv_signed imm) 8 v -> 0 <= v < 2 ^ 64 ->
  (forall ms' mat',
     st_ok segs (havoc E K [Z_to_bv 64 v]) (set_regs_pc ss [(rd, SOff K 0)] (ss_pc ss + 4)) (restrict (w_H W) ms') ->
     ms_mem ms' = ms_mem ms ->
     SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
intros W E ss ms md rd rs imm w base v K Q HS Hrv Hat Hlk Hdec Hrd Hb Hb0 Ha0 Ha8 Hv Hv0 Hk.
assert (A1 : base + bv_signed imm + Z.of_nat 8 <= 2 ^ 64) by (cbn; lia).
assert (A2 : 0 <= v < 2 ^ (8 * Z.of_nat 8)) by (cbn; lia).
destruct (smb_rdn_val _ _ 8 v Hv Ha0 A1 A2) as [Hrdn Hbs].
apply (smb_hld8 W E ss ms md rd rs imm w (base + bv_signed imm) (Z_to_le_bytes 8 v) (Z_to_bv 64 v) K Q HS Hrv Hat Hlk Hdec Hrd).
- rewrite Hb. apply smb_vaddi; lia.
- exact Hrdn.
- rewrite Hbs, unsigned_lit_small by lia. reflexivity.
- exact Hk.
Qed.

Lemma smb_hlwv : forall (W : world segs) E ss ms md (rd rs : bv 5) (imm : bv 12) (w base v : Z) (K : nat)
  (Q : world segs -> config -> Prop),
  st_ok segs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
  clookup tbl (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ4 true rd rs imm, 4) ->
  bv_eqb rd 0 = false ->
  sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 base -> 0 <= base < 2 ^ 64 ->
  0 <= base + bv_signed imm -> base + bv_signed imm + 4 <= 2 ^ 64 ->
  YI04.val_mem segs (mrestrict (w_H W) (ms_mem ms)) (base + bv_signed imm) 4 v -> 0 <= v < 2 ^ 31 ->
  (forall ms' mat',
     st_ok segs (havoc E K [Z_to_bv 64 v]) (set_regs_pc ss [(rd, SOff K 0)] (ss_pc ss + 4)) (restrict (w_H W) ms') ->
     ms_mem ms' = ms_mem ms ->
     SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
intros W E ss ms md rd rs imm w base v K Q HS Hrv Hat Hlk Hdec Hrd Hb Hb0 Ha0 Ha8 Hv Hv0 Hk.
assert (A1 : base + bv_signed imm + Z.of_nat 4 <= 2 ^ 64) by (cbn; lia).
assert (A2 : 0 <= v < 2 ^ (8 * Z.of_nat 4)) by (cbn; lia).
destruct (smb_rdn_val _ _ 4 v Hv Ha0 A1 A2) as [Hrdn Hbs].
apply (smb_hlw W E ss ms md rd rs imm w (base + bv_signed imm) (Z_to_le_bytes 4 v) (Z_to_bv 64 v) K Q HS Hrv Hat Hlk Hdec Hrd).
- rewrite Hb. apply smb_vaddi; lia.
- exact Hrdn.
- rewrite Hbs, unsigned_lit_small by lia. reflexivity.
- intros ms' mat' HS' Hm. rewrite v_lw_small in HS' by (rewrite unsigned_lit_small by lia; lia). exact (Hk ms' mat' HS' Hm).
Qed.
End h.

Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
(* a step that writes nothing keeps the journal through the materialized model *)
Lemma smb_aj_wvb : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k mat,
  ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc
    (with_vm_backing (m_vm_lazy mdc) mat mdc) k.
Proof.
intros STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k mat HJ.
apply (ajournal_x_exec segs B PST ARx LAWS segs_low STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k memc
  (with_vm_backing (m_vm_lazy mdc) mat mdc) (fun _ => False) HJ).
- intros x _. reflexivity.
- apply mem_grows_refl.
- intros x _. reflexivity.
- unfold same_but_materialized. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]. reflexivity.
- intros a [].
Qed.
End j.

Section p.
Variable segs : list Segment.
(* the i-th item / member of a container *)
Lemma smb_items_nth : forall (P : Z -> jv -> list (Z * Z) -> Prop) l a D i u,
  pj_itemsR P a l D -> nth_error l i = Some u -> exists D1, incl D1 D /\ P (a + 56 * Z.of_nat i) u D1.
Proof.
intros P l. induction l as [|v r IH]; intros a D i u H E; [destruct i; discriminate|].
cbn [pj_itemsR] in H. destruct H as (D1 & D2 & ED & HP & HR).
destruct i as [|i]; cbn in E.
- injection E as <-. exists D1. split; [subst D; intros b Hb; apply in_or_app; left; exact Hb|].
  replace (a + 56 * Z.of_nat 0) with a by lia. exact HP.
- destruct (IH (a + 56) D2 i u HR E) as (D3 & Hinc & HP3). exists D3.
  split; [subst D; intros b Hb; apply in_or_app; right; apply Hinc; exact Hb|].
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact HP3.
Qed.

Lemma smb_mems_nth : forall m L (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D i nm u,
  pj_memsR segs m L P a ka l D -> nth_error l i = Some (nm, u) ->
  exists x k D1, incl D1 D /\ In (x, k) D /\ rd_u64 segs m (ka + 8 * Z.of_nat i) x /\
    pj_cstrR segs m L x k nm /\ P (a + 56 * Z.of_nat i) u D1.
Proof.
intros m L P l. induction l as [|[nm0 v] r IH]; intros a ka D i nm u H E; [destruct i; discriminate|].
cbn [pj_memsR] in H. destruct H as (x & k & D1 & D2 & ED & Hx & Hc & HP & HR).
destruct i as [|i]; cbn in E.
- injection E as E1 E2. subst nm0 v. exists x, k, D1.
  split; [subst D; intros b Hb; right; apply in_or_app; left; exact Hb|].
  split; [subst D; left; reflexivity|].
  replace (ka + 8 * Z.of_nat 0) with ka by lia. replace (a + 56 * Z.of_nat 0) with a by lia. auto.
- destruct (IH (a + 56) (ka + 8) D2 i nm u HR E) as (x' & k' & D3 & Hinc & Hin & Hx' & Hc' & HP').
  exists x', k', D3.
  split; [subst D; intros b Hb; right; apply in_or_app; right; apply Hinc; exact Hb|].
  split; [subst D; right; apply in_or_app; right; exact Hin|].
  replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. auto.
Qed.

(* a child's footprint lies in its parent's *)
Lemma smb_foot_sub : forall p D kids c D1 (i : nat) a,
  In (kids, c) D -> incl D1 D -> 56 * Z.of_nat i + 56 <= c ->
  pj_footR (kids + 56 * Z.of_nat i) D1 a -> pj_footR p D a.
Proof.
intros p D kids c D1 i a Hk Hinc H1 [Ha | (b & Hb & Ha)].
- right. exists (kids, c). split; [exact Hk | unfold pj_holdsR; cbn [fst snd]; lia].
- right. exists b. split; [apply Hinc; exact Hb | exact Ha].
Qed.

(* depth *)
Lemma smb_depth_nth : forall items i u, nth_error items i = Some u -> (depth u < depth (JArr items))%nat.
Proof.
intros items i u E. cbn [depth]. apply Nat.lt_succ_r. revert i E. induction items as [|v r IH]; intros i E; [destruct i; discriminate|].
destruct i as [|i]; cbn in E |- *.
- injection E as <-. apply Nat.le_max_l.
- eapply Nat.le_trans; [apply (IH i E) | apply Nat.le_max_r].
Qed.
Lemma smb_depth_nthm : forall members i nm u, nth_error members i = Some (nm, u) -> (depth u < depth (JObj members))%nat.
Proof.
intros members i nm u E. cbn [depth]. apply Nat.lt_succ_r. revert i E. induction members as [|[n0 v] r IH]; intros i E; [destruct i; discriminate|].
destruct i as [|i]; cbn in E |- *.
- injection E as <- <-. apply Nat.le_max_l.
- eapply Nat.le_trans; [apply (IH i E) | apply Nat.le_max_r].
Qed.

Lemma smb_tag_range : forall t, 0 <= tag t <= 6.
Proof. destruct t; cbn; lia. Qed.

Lemma smb_list_eq_nth : forall (A : Type) (l l' : list A), length l = length l' ->
  (forall i, (i < length l)%nat -> nth_error l i = nth_error l' i) -> l = l'.
Proof.
intros A l. induction l as [|x l IH]; intros [|y l'] Hl H; cbn in Hl; try lia; [reflexivity|].
f_equal.
- specialize (H 0%nat ltac:(cbn; lia)). cbn in H. congruence.
- apply IH; [lia|]. intros i Hi. apply (H (S i)). cbn; lia.
Qed.
End p.

Lemma smb_SO8 : SHADOW_OFF mod 64 = 0.
Proof. reflexivity. Qed.
Lemma smb_nz8 : 8 <> 0. Proof. discriminate. Qed.
Lemma smb_nz64 : 64 <> 0. Proof. discriminate. Qed.
Lemma smb_pos8 : 0 < 8. Proof. reflexivity. Qed.
Lemma smb_pos64 : 0 < 64. Proof. reflexivity. Qed.

(* a block shadow gives every sub-range of its bytes *)
Lemma smb_ra_of_bshadow : forall (rd : Z -> option Z) p n x len,
  block_shadow rd SHADOW_OFF p n -> p <= x -> x + len <= p + n -> range_addressable rd SHADOW_OFF x len.
Proof.
intros rd p n x len (Hp & Hn & Hb) Hx Hxl y Hy.
assert (Ep : p = 8 * (p / 8)) by (pose proof (Z.div_mod p 8 smb_nz8); lia).
set (i := (y - p) / 8).
assert (Hi0 : 0 <= i) by (apply Z.div_pos; lia).
assert (Ey : y / 8 = p / 8 + i).
{ unfold i. replace y with ((p / 8) * 8 + (y - p)) at 1 by lia. rewrite Z.div_add_l by lia. reflexivity. }
assert (Hi : i < (n + 7) / 8) by (unfold i; apply Z.div_lt_upper_bound; [lia|]; pose proof (Z.div_mod (n + 7) 8 smb_nz8); pose proof (Z.mod_pos_bound (n + 7) 8 smb_pos8); lia).
pose proof (Hb i (conj Hi0 Hi)) as Hs. unfold shadow_of_addr in *. rewrite Ey, Z.add_assoc.
eexists. split; [exact Hs|].
destruct (Z.ltb_spec i (n / 8)) as [Hl|Hl]; [left; reflexivity|right].
pose proof (Z.div_mod n 8 smb_nz8) as Dn. pose proof (Z.mod_pos_bound n 8 smb_pos8) as Mn.
pose proof (Z.div_mod (y - p) 8 smb_nz8) as Dy. pose proof (Z.mod_pos_bound (y - p) 8 smb_pos8) as My.
fold i in Dy.
assert (Hi' : i < n / 8 + 1) by lia.
assert (Ei : i = n / 8) by lia.
assert (Hym : y mod 8 = (y - p) mod 8).
{ rewrite Ep. replace (y - 8 * (p / 8)) with (y + (- (p / 8)) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
rewrite Hym. lia.
Qed.

Lemma smb_ra_sub : forall (rd : Z -> option Z) Bz x n y m,
  range_addressable rd Bz x n -> x <= y -> y + m <= x + n -> range_addressable rd Bz y m.
Proof. intros rd Bz x n y m H H1 H2 z Hz. apply H. lia. Qed.

Lemma smb_ra_keep : forall (rd rd' : Z -> option Z) Bz x n,
  range_addressable rd Bz x n -> (forall y, x <= y < x + n -> rd' (shadow_of_addr Bz y) = rd (shadow_of_addr Bz y)) ->
  range_addressable rd' Bz x n.
Proof. intros rd rd' Bz x n H E y Hy. destruct (H y Hy) as (s & Hs & Hok). exists s. rewrite E by exact Hy. auto. Qed.

Lemma smb_ra_zero : forall (rd : Z -> option Z) Bz x n,
  (forall y, x <= y < x + n -> rd (shadow_of_addr Bz y) = Some 0) -> range_addressable rd Bz x n.
Proof. intros rd Bz x n H y Hy. exists 0. split; [exact (H y Hy) | left; reflexivity]. Qed.

Lemma smb_hull_sub : forall (rd : Z -> option Z) x n y m,
  shadow_hull_vis rd x n -> x <= y -> y + m <= x + n -> 0 < m -> shadow_hull_vis rd y m.
Proof.
intros rd x n y m H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
assert (A1 : (SHADOW_OFF + x / 8) / 8 * 8 <= (SHADOW_OFF + y / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (A2 : (SHADOW_OFF + (y + m - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.

Lemma smb_hull_keep : forall (rd rd' : Z -> option Z) x n,
  shadow_hull_vis rd x n ->
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
  shadow_hull_vis rd' x n.
Proof. intros rd rd' x n H E s Hs. rewrite E by exact Hs. exact (H s Hs). Qed.

(* the hull of a sub-range of a 64-aligned range whose shadow bytes are all present *)
Lemma smb_hull_al64 : forall (rd : Z -> option Z) lo hi y m,
  lo mod 64 = 0 -> hi mod 64 = 0 -> lo <= y -> y + m <= hi -> 0 < m ->
  (forall a, lo <= a < hi -> a mod 8 = 0 -> rd (SHADOW_OFF + a / 8) <> None) -> shadow_hull_vis rd y m.
Proof.
intros rd lo hi y m Hlo Hhi H1 H2 H3 Hp s Hs. unfold shadow_addr in Hs.
assert (EO : SHADOW_OFF = 8 * (SHADOW_OFF / 8)) by reflexivity.
assert (D1 : (SHADOW_OFF + y / 8) / 8 = SHADOW_OFF / 8 + y / 64).
{ rewrite EO at 1. rewrite Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_div by lia. reflexivity. }
assert (D2 : (SHADOW_OFF + (y + m - 1) / 8) / 8 = SHADOW_OFF / 8 + (y + m - 1) / 64).
{ rewrite EO at 1. rewrite Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_div by lia. reflexivity. }
rewrite D1, D2 in Hs.
assert (L1 : lo / 64 <= y / 64) by (apply Z.div_le_mono; lia).
assert (L2 : (y + m - 1) / 64 < hi / 64) by (apply Z.div_lt_upper_bound; [lia|]; pose proof (Z.div_mod hi 64 smb_nz64); lia).
pose proof (Z.div_mod lo 64 smb_nz64) as Dlo. pose proof (Z.div_mod hi 64 smb_nz64) as Dhi.
set (a := 8 * (s - SHADOW_OFF)).
assert (Ea : a / 8 = s - SHADOW_OFF) by (unfold a; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
replace s with (SHADOW_OFF + a / 8) by lia. apply Hp; [|unfold a; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity].
unfold a. lia.
Qed.

(* two readers agree on a byte outside the image when their views agree (PRH_Reader.pj_agreeR's pointwise form) *)
Lemma smb_agree_of_aview : forall segs H H' (m m' : word -> option byte) z,
  0 <= z < 2 ^ 64 -> ~ in_img segs z -> aview segs H' m' z = aview segs H m z ->
  mbyte segs (mrestrict H' m') z = mbyte segs (mrestrict H m) z /\
  (writable_at segs (mrestrict H m) z -> writable_at segs (mrestrict H' m') z).
Proof.
intros segs H H' m m' z Hz Hni E. unfold aview in E.
assert (E2 : mbyte segs (mrestrict H' m') z = mbyte segs (mrestrict H m) z).
{ destruct (mbyte segs (mrestrict H' m') z) as [b'|] eqn:A; destruct (mbyte segs (mrestrict H m) z) as [b|] eqn:Bq;
    cbn in E; try discriminate; [|reflexivity]. injection E as E. f_equal. apply bv_eq. exact E. }
split; [exact E2|]. intros Hw. unfold writable_at, wview in *.
assert (Hn : find_segment segs (bv_unsigned (Z_to_bv 64 z)) 1 = None).
{ rewrite unsigned_lit_small by lia. destruct (find_segment segs z 1) as [sg|] eqn:F; [|reflexivity].
  exfalso. apply Hni. pose proof (find_segment_some_spec segs z 1 sg F) as (Hin & Hlo & Hhi). exists sg. split; [exact Hin | lia]. }
rewrite Hn in Hw |- *. unfold mbyte in E2.
assert (Hr : seg_rom segs (Z_to_bv 64 z) = None) by (unfold seg_rom, memory_read; cbn [Z.of_N]; rewrite Hn; reflexivity).
destruct (mrestrict H m (Z_to_bv 64 z)) as [b|] eqn:Mb; [|destruct (Hw eq_refl)].
destruct (mrestrict H' m' (Z_to_bv 64 z)) as [b'|] eqn:Mb'; [discriminate|].
rewrite Hr in E2. discriminate.
Qed.

(* ---- (3) the entry state of a function whose prologue is `addi sp, sp, -f` (port-fm FMW_K.v:36-68 over afn_pre_x) ---- *)
Definition smbk_fstk (f : Z) : YP09.region := YP09.mkRegion (Some 2%nat) (- f) 0 (- f) 0 [].
Definition smbk_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition smbk_ss0 (pc f : Z) : sstate := mkSS pc sr_atoms [smbk_fstk f] None smbk_facts.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma smbk_sp : forall segs B ARx STK ly S Hp (W : world segs) regs mem md ch,
  afn_pre_x segs B ARx STK ly S Hp W regs mem md ch ->
  spZ regs mod 16 = 0 /\ YM05.alloc_ceiling + STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\ 0 <= STK.
Proof.
intros segs B ARx STK ly S Hp W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop). lia.
Qed.
Lemma smbk_entry : forall segs B ARx STK f ly S Hp (W : world segs) regs mem md ch pc,
  afn_pre_x segs B ARx STK ly S Hp W regs mem md ch -> 0 <= f <= STK -> regions_wf [smbk_fstk f] = true ->
  st_ok segs (Ereg regs []) (smbk_ss0 pc f) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs))).
Proof.
intros segs B ARx STK f ly S Hp W regs mem md ch pc HPRE Hf Hwf.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (smbk_sp segs B ARx STK ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
rewrite restrict_mkst_fx.
assert (E2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold smbk_ss0. apply (entry_st_ok_full segs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor].
  apply (region_ok_stack segs _ _ 2 (spZ regs) (- f) E2); [lia | lia |].
  intros a Ha. apply (apresent_writable segs). apply Hpres. lia.
- cbn. tauto.
- unfold smbk_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia | split; [exact Hal16 | lia]].
Qed.
Lemma smbk_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. apply bv_eq. rewrite denot_SOff, Z.add_0_r. apply zcanon_id. unfold M64. apply u64_range.
Qed.
(* a run whose write windows all lie at or above YM05.alloc_ceiling (the stack) leaves every byte below it as it was *)
Lemma smbk_frame_below : forall segs E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> YM05.alloc_ceiling <= a) ->
  forall a, 0 <= a < YM05.alloc_ceiling -> mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof.
intros segs E rs H m m' HF Hrs a Ha. pose proof asan_consts as (C1 & _). unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. intros Hw. pose proof (Hrs a Hw). lia.
Qed.
End e.


(* ---- the alloc.c ledger across memory that agrees below YM05.alloc_ceiling (port-fm FMW_K.v:103-117 fm_glob_below, over
   PRH_Base's prh_ledger at image B's PrhImg prh_img_B): the statics are image bytes, every harness head lies in a live
   allocator block, and both are below YM05.alloc_ceiling (AR_laws_x's blocks law) ---- *)
Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Lemma smbk_val_mem_keep : forall (m m' : word -> option byte) a (n : nat) v,
  val_mem segs m a n v -> (forall k, (k < n)%nat -> mbyte segs m' (a + Z.of_nat k) = mbyte segs m (a + Z.of_nat k)) ->
  val_mem segs m' a n v.
Proof. intros m m' a n v Hv Hk k Hkn. rewrite (Hk k Hkn). exact (Hv k Hkn). Qed.
Lemma smbk_ledger_keep : forall ly S Hp (W : world segs) mem md mem' Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> mbyte segs (mrestrict (w_H W) mem') a = mbyte segs (mrestrict (w_H W) mem) a) ->
  prh_ledger (PI := prh_img_B) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR
  ((G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & GR) & HN & HF & HP) Hm.
pose proof asan_consts as (C1 & _).
assert (VB : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= YM05.alloc_ceiling ->
  val_mem segs (mrestrict (w_H W) mem) a n v -> val_mem segs (mrestrict (w_H W) mem') a n v).
{ intros a n v Ha Hb Hv. apply (smbk_val_mem_keep _ _ a n v Hv). intros k Hk. apply Hm. lia. }
pose proof (@alloc_ceiling_val rc) as [[Hac0 _] Hac].
split.
{ unfold prh_glob, prh_most, prh_own.
  cbn [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out
    pi_gz_live pi_gz_peak pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_B] in *.
  split; [apply VB; [lia | cbn; lia | exact G1]|].
  split; [apply VB; [lia | cbn; lia | exact G2]|].
  split; [apply VB; [lia | cbn; lia | exact G3]|].
  split; [apply VB; [lia | cbn; lia | exact G4]|].
  split; [apply VB; [lia | cbn; lia | exact G5]|].
  split; [split; [apply VB; [lia | cbn; lia | exact G6] | exact G6r]|].
  split; [split; [apply VB; [lia | cbn; lia | exact G7] | exact G7r] | exact GR]. }
split; [exact HN|]. split; [|exact HP].
eapply Forall_impl; [|exact HF]. intros [a k] (Hk & Hin & Hhp & Hal & Hv). cbn [fst snd] in *.
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hin) as (H16 & H4096 & Hc & _).
pose proof (@cf_head_nonneg cp) as Hch0.
assert (Hr : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
split; [exact Hk|]. split; [exact Hin|]. split; [exact Hhp|]. split; [exact Hal|].
apply VB; [lia | | exact Hv]. cbn. lia.
Qed.
End l.


(* the state stops at a branch it cannot decide: split on it *)
Ltac smbk_branch tbl HS :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_step segs tbl ss) in
    lazymatch r with
    | SStop (SR_branch ?c ?a ?b) =>
      apply (SRr_sym_branch segs W E ss ms _ _ c a b HS); clear HS
    | _ => fail "smbk_branch: not stopped at a branch:" r
    end
  end.
