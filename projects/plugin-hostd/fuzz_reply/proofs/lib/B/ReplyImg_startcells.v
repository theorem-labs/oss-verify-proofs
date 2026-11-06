(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, reply image B's start witness of the cf layer's two machine cells
   (start_cells_cf, field round 2: YG0ncf.v / YGcfInstBase.v exh_cell_cf_init / errb_cells_cf_init), stated in this
   tree's own names at every world W' with wle W W' above the start-up hand-off world W:
   EXH: the 31 per-class exhausted bytes (RegionInfo + 128 c + cf_exh_off) read 0, from AR's region_cells (YG0n.v).
   No function is proved here. *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane M, CfInstHit; Main's errbuf / start-cells ruling): the error
   buffer's five cells are no longer const cells of AR: B/YF0m.v is regenerated without them (the walks write the
   object, so it cannot be constant), and their start values come from the start-up hand-off instead:
   ERRB: the five 8-byte cells (cf_errbuf_obj + 0 / 16 / 32 / 40 / 48) read 0 at the hand-off memory, from
   B/ReplyImg_su_errb.v errb_obj_zero_start (the object's 56 bytes are .bss under a KImg range in every hand-off
   state), and so at every world above it (YA0o.v mbyte_mrestrict_hsub).
   PF (field round 3, start_pf_cf): Printf's two image cells hold their start values at the hand-off memory: the
   tool-name pointer cf_toolname_cell = 0x9fe38 holds cf_toolname_val = 0x2036f, and the callback cell cf_pfcb_cell =
   0x138350 holds cf_pfcb_val = 0x56418 (AppendToErrorMessageBuffer). Each of the 50 hand-off states (YB01.v) knows
   both words (KWord; checked by computation below, the twins of B/ReplyImg_su_tool.v su_tool_cell_B and
   B/ReplyImg_su_printf.v), and B/YD2k.v finv_read_val turns a known word into the bytes at the hand-off memory.
   Kind: START-UP fact; rule 24: no function proved. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h YB13 YB01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r YG0b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1g YD2i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0d YI04 YI00 YE00 YA0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YB1v YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_su_errb YD2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YK04 YA0n YG00 YG01 YG0f YG0v YG0n YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YF0x CfImgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* The five error-buffer cells of the cf layer's errb_cells_cf at the start state (cf_errbuf_obj + 0 / 16 / 32 / 40 / 48). *)
Definition errb_start_cells_B : list acell :=
  map (fun d => z8 (ANum (@cf_errbuf_obj CfImg_B + d)) 0) [0; 16; 32; 40; 48].

Lemma start_exh_B : forall ly S (W : world tfibsegs) mem md,
  AR tfibsegs B ly S W mem md ->
  forall W' : world tfibsegs, wle W W' -> forall c, 1 <= c <= 31 ->
  cell_holds B ly (aview tfibsegs (w_H W') mem) (z1 (aoff (ASp (kRegionInfoOff + 128 * c)) (@cf_exh_off CfImg_B)) 0).
Proof.
intros ly S W mem md HAR W' Hle c Hc.
pose proof (Forall_cell_holds_ext B ly _ _ _ (aview_ext tfibsegs (w_H W) (w_H W') mem (w_Hoff W) Hle) (am_cells B ly S _ (proj1 HAR))) as CL.
apply (proj1 (Forall_forall _ _) CL). unfold acells. apply in_app_iff. left.
apply in_flat_map. exists c. split.
- unfold zseq. apply in_map_iff. exists (Z.to_nat (c - 1)). split; [lia|]. apply in_seq. lia.
- unfold region_cells. do 8 right. left. reflexivity.
Qed.

(* An 8-byte value at the memory of a world W is the value of its z8 cell at every world above W: wle W W' hides
   fewer bytes, and a byte that reads at W reads the same at W' (YA0o.v mbyte_mrestrict_hsub). *)
Lemma ho_z8 : forall ly (W W' : world tfibsegs) mem a v, wle W W' ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a 8 v ->
  cell_holds B ly (aview tfibsegs (w_H W') mem) (z8 (ANum a) v).
Proof.
intros ly W W' mem a v Hle V k Hk. cbn [z8 c8 c_at c_val c_w aeval]. unfold aview.
rewrite (mbyte_mrestrict_hsub tfibsegs (w_H W) (w_H W') mem _ _ (w_Hoff W) Hle (V k Hk)). cbn [option_map].
rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [reflexivity|]. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
End s.

(* Printf's two cells in every hand-off state's knowledge: each state reads the tool-name word and the callback word
   at their start values (computation over YB01.v's 50 states, as B/ReplyImg_su_tool.v su_tool_hs_all). *)
Definition su_pf_ok (ch : acs) : bool :=
  match kn_read tfibsegs ch (ELit 0) (@cf_toolname_cell CfImg_B) 8, kn_read tfibsegs ch (ELit 0) (@cf_pfcb_cell CfImg_B) 8 with
  | Some e1, Some e2 => (expr_eqb e1 (ELit (@cf_toolname_val CfImg_B)) && expr_eqb e2 (ELit (@cf_pfcb_val CfImg_B)))%bool
  | _, _ => false
  end.

Lemma su_pf_ok_sound : forall ch, su_pf_ok ch = true ->
  kn_read tfibsegs ch (ELit 0) (@cf_toolname_cell CfImg_B) 8 = Some (ELit (@cf_toolname_val CfImg_B)) /\
  kn_read tfibsegs ch (ELit 0) (@cf_pfcb_cell CfImg_B) 8 = Some (ELit (@cf_pfcb_val CfImg_B)).
Proof.
intros ch H. unfold su_pf_ok in H.
destruct (kn_read tfibsegs ch (ELit 0) (@cf_toolname_cell CfImg_B) 8) as [e1|]; [|discriminate H].
destruct (kn_read tfibsegs ch (ELit 0) (@cf_pfcb_cell CfImg_B) 8) as [e2|]; [|discriminate H].
apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. subst e1 e2. split; reflexivity.
Qed.

Lemma su_pf_hs_all : forallb su_pf_ok HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.

(* The hand-off: YD2k.v's Section e, copied verbatim, with a world W whose hidden set is the hand-off's. *)
Section c. Context {fx : YK11.FPState}.
Section e.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TSEGS TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Context {rc : YM05.RunCeil}.
Variable W : world tfibsegs.
Hypothesis HW : w_H W = YD2i.H1 sp rdraw inp ch E model.

(* ERRB: the five cells read 0 at every world above the hand-off. *)
Lemma start_errb_B : forall B ly (W' : world tfibsegs), wle W W' ->
  Forall (cell_holds B ly (aview tfibsegs (w_H W') FULL)) errb_start_cells_B.
Proof.
intros B ly W' Hle.
pose proof (ReplyImg_su_errb.errb_obj_zero_start sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC) as Z0.
apply Forall_forall. intros x Hx. unfold errb_start_cells_B in Hx. apply in_map_iff in Hx as (d & <- & Hd).
apply (ho_z8 B ly W W' FULL); [exact Hle|]. rewrite HW.
assert (Hd' : 0 <= d <= 48) by (cbn in Hd; lia).
intros k Hk.
pose proof (Z0 (Z.to_nat d + k)%nat ltac:(lia)) as Zk.
replace (@cf_errbuf_obj CfImg_B + d + Z.of_nat k) with (ReplyImg_su_errb.ERRB_OBJ + Z.of_nat (Z.to_nat d + k))
  by (cbn [cf_errbuf_obj CfImg_B]; unfold ReplyImg_su_errb.ERRB_OBJ; lia).
rewrite Zk. f_equal. f_equal. cbv [YO0f.le_byte YG0f.le_byte].
rewrite !Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite !Z.shiftr_0_l. reflexivity.
Qed.

(* PF: Printf's two cells hold their start values at every world above the hand-off. *)
Lemma start_pf_cells_B : forall B ly (W' : world tfibsegs), wle W W' ->
  cell_holds B ly (aview tfibsegs (w_H W') FULL) (z8 (ANum (@cf_toolname_cell CfImg_B)) (@cf_toolname_val CfImg_B)) /\
  cell_holds B ly (aview tfibsegs (w_H W') FULL) (z8 (ANum (@cf_pfcb_cell CfImg_B)) (@cf_pfcb_val CfImg_B)).
Proof.
intros B ly W' Hle.
destruct (su_pf_ok_sound ch (proj1 (forallb_forall _ _) su_pf_hs_all ch (HS_tfib_In h ch Hch))) as [R1 R2].
pose proof (YD2k.finv_read_val sp rdraw brk inp Hsp Hva ch E R FULL model HC _ _ _ R1 ltac:(cbn; lia)) as V1.
pose proof (YD2k.finv_read_val sp rdraw brk inp Hsp Hva ch E R FULL model HC _ _ _ R2 ltac:(cbn; lia)) as V2.
rewrite uE_litv in V1 by (cbn; lia). rewrite uE_litv in V2 by (cbn; lia).
split; (apply (ho_z8 B ly W W' FULL); [exact Hle|]); rewrite HW; [exact V1 | exact V2].
Qed.
End e.
End c.
