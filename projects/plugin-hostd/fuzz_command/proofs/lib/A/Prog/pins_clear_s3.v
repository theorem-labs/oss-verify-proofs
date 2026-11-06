(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of pins_clear's ASan walk on plugin-hostd/fuzz_command
   (the inlined record(), recorder.c:205-221), after proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v (cl_A_okX, the
   entry segment of the cgif_close walk) over fuzz_command's listing. *)

(* pins_clear's entry segment runs 0x8ccb4 .. 0x8cd2c: the 64-byte frame and the callee-saved stores, the shadow
   base from the GOT cell 0xa63f0, g_rec.ncalls, and then record()'s test of the call count against 16.
   - the table arm (0x8cd10): g_rec.ncalls := ncalls + 1 and the slot is g_rec.calls[ncalls];
   - the spill arm (0x8ccf8): rec_calls_free(&record.spill, 1) frees the arguments the spill held, and the slot
     is record.spill.
   Both arms meet at 0x8cd2c, which this segment hands to its continuation together with `pcl_at_join`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaNoChain PaDenot PaSB PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas pins_clear_s1 pins_clear_s2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c pins_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee this segment reaches, and the bridge from the image's objects to the listing's atoms *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's per-binary hypotheses, with the statements' names, shared by every recorder walk *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* the footprint of the whole call: g_rec, record.spill and the recorder's own blocks *)
Definition pcl3_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* --- the facts the segment's glue needs ------------------------------------------------------------- *)

Lemma pcl3_inFP_grec : forall O a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP (pcl3_FP O) a.
Proof.
intros O a Ha. exists (A_G_REC, A_G_REC + REC_SIZE).
split; [left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

Lemma pcl3_inFP_spill : forall O a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP (pcl3_FP O) a.
Proof.
intros O a Ha. exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE).
split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

Lemma pcl3_inFP_blk : forall O p n i, In (p, n) O -> 0 <= i < req_size n -> inFP (pcl3_FP O) (p + i).
Proof.
intros O p n i Hin Hi. destruct (inFP_ablocks_fp O p n i Hin Hi) as (r & Hr & Hb).
exists r. split; [right; right; exact Hr | exact Hb].
Qed.

(* a g_rec / record.spill byte of the footprint is a byte the walk may write *)
Lemma pcl3_awr_grec : forall STK sp0 O bl0 blc fr0 lyx own a,
A_G_REC <= a < A_G_REC + REC_SIZE -> awr_byte SEGS B STK sp0 (pcl3_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyx own a Ha.
right; right; right; right; left.
split; [exact (pcl3_inFP_grec O a Ha)|].
split; [rewrite (recb_ts_prog_m B HB); exact (recb_grec_in a Ha)
       | exact (cmd_prog_img a (recb_grec_in a Ha))].
Qed.

Lemma pcl3_awr_spill : forall STK sp0 O bl0 blc fr0 lyx own a,
A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> awr_byte SEGS B STK sp0 (pcl3_FP O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyx own a Ha.
right; right; right; right; left.
split; [exact (pcl3_inFP_spill O a Ha)|].
split; [rewrite (recb_ts_prog_m B HB); exact (recb_spill_in a Ha)
       | exact (cmd_prog_img a (recb_spill_in a Ha))].
Qed.

(* reading the symbolic state back *)
Lemma pcl3_zcanon : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x.
Proof. intros x Hx. unfold zcanon, M64. apply Z.mod_small. exact Hx. Qed.
Lemma pcl3_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma pcl3_denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma pcl3_bv64 : forall (w : word), 0 <= bv_unsigned w < 2 ^ 64.
Proof.
intros w. pose proof (bv_unsigned_in_range 64 w) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Hb. lia.
Qed.

Lemma pcl3_region_nth : forall E ss ms i r,
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi.
exact (st_ok_region_nth (segs := SEGS) E (abs_ss VAL ss) ms i r HS ltac:(destruct ss; exact Hi)).
Qed.

(* the slot of record()'s table arm: g_rec + 16 + 56 * ncalls, as the executor folds it *)
Lemma pcl3_denot_slot : forall E n,
ew E PCL_N = Z_to_bv 64 n -> 0 <= n <= 16 -> ew E PCL_GR = Z_to_bv 64 A_G_REC ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff PCL_N 0) (SLit 56)) (SLit 16)) (SOff PCL_GR 0))
= Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros E n HN Hn HG. apply pcl3_denot_U.
assert (U1 : U E (SOff PCL_N 0) = n) by (apply (U_atom E PCL_N n HN); lia).
assert (U5 : U E (SOff PCL_GR 0) = A_G_REC) by (apply (U_atom E PCL_GR A_G_REC HG); unfold A_G_REC; lia).
rewrite U_SAlu, U_SAlu, U_SMd, U1, U5, !U_SLit.
cbn [zalu_raw zmd_raw].
rewrite (pcl3_zcanon 56), (pcl3_zcanon 16) by lia.
rewrite (pcl3_zcanon (n * 56)) by lia.
rewrite (pcl3_zcanon (n * 56 + 16)) by lia.
unfold A_G_REC, OFF_CALLS, CALL_SIZE. rewrite pcl3_zcanon by lia. lia.
Qed.

(* a word of the frame, from the walk's stack region *)
Lemma pcl3_frame_field : forall E (W : world SEGS) m sp0 (regs : bvmap 5 word) cs lo hi wlo whi off
  (rn : nat) (r : bv 5),
region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = sp0 -> ew E rn = getr regs r ->
In (YP09.mkChunk off (CVal 8 (SOff rn 0))) cs ->
aval_mem (aview SEGS (w_H W) m) (sp0 + off) 8 (bv_unsigned (getr regs r)).
Proof.
intros E W m sp0 regs cs lo hi wlo whi off rn r HR Hsp Hew Hin.
apply (aval_mem_view SEGS). change 8%nat with (N.to_nat 8).
apply (field_of_region E (mrestrict (w_H W) m) 2%nat sp0 cs lo hi wlo whi off 8 (SOff rn 0)
  (bv_unsigned (getr regs r)) HR Hsp Hin).
- rewrite pcl3_soff0, Hew. symmetry. apply Z_to_bv_bv_unsigned.
- rewrite pcl_pow8. apply pcl3_bv64.
- cbn. lia.
Qed.

Lemma pcl3_frame_of_region : forall E (W : world SEGS) m sp0 (regs : bvmap 5 word) lo hi wlo whi cs,
region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = sp0 ->
(forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs rr) ->
In (YP09.mkChunk (-56) (CVal 8 (SOff 21 0))) cs ->
In (YP09.mkChunk (-48) (CVal 8 (SOff 20 0))) cs ->
In (YP09.mkChunk (-40) (CVal 8 (SOff 19 0))) cs ->
In (YP09.mkChunk (-32) (CVal 8 (SOff 18 0))) cs ->
In (YP09.mkChunk (-24) (CVal 8 (SOff 9 0))) cs ->
In (YP09.mkChunk (-16) (CVal 8 (SOff 8 0))) cs ->
In (YP09.mkChunk (-8) (CVal 8 (SOff 1 0))) cs ->
pcl_frame_at (aview SEGS (w_H W) m) (sp0 - PCL_FRAME)
  (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
  (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))
  (bv_unsigned (getr regs 21)).
Proof.
intros E W m sp0 regs lo hi wlo whi cs HR Hsp Hew I21 I20 I19 I18 I9 I8 I1.
unfold pcl_frame_at, PCL_FRAME.
pose proof (pcl3_bv64 (getr regs 1)). pose proof (pcl3_bv64 (getr regs 8)).
pose proof (pcl3_bv64 (getr regs 9)). pose proof (pcl3_bv64 (getr regs 18)).
pose proof (pcl3_bv64 (getr regs 19)). pose proof (pcl3_bv64 (getr regs 20)).
pose proof (pcl3_bv64 (getr regs 21)).
repeat apply conj; try lia.
- replace (sp0 - 64 + 8) with (sp0 + (-56)) by lia.
  exact (pcl3_frame_field E W m sp0 regs cs lo hi wlo whi (-56) 21%nat 21%bv HR Hsp
    (Hew 21%nat 21%bv eq_refl) I21).
- replace (sp0 - 64 + 16) with (sp0 + (-48)) by lia.
  exact (pcl3_frame_field E W m sp0 regs cs lo hi wlo whi (-48) 20%nat 20%bv HR Hsp
    (Hew 20%nat 20%bv eq_refl) I20).
- replace (sp0 - 64 + 24) with (sp0 + (-40)) by lia.
  exact (pcl3_frame_field E W m sp0 regs cs lo hi wlo whi (-40) 19%nat 19%bv HR Hsp
    (Hew 19%nat 19%bv eq_refl) I19).
- replace (sp0 - 64 + 32) with (sp0 + (-32)) by lia.
  exact (pcl3_frame_field E W m sp0 regs cs lo hi wlo whi (-32) 18%nat 18%bv HR Hsp
    (Hew 18%nat 18%bv eq_refl) I18).
- replace (sp0 - 64 + 40) with (sp0 + (-24)) by lia.
  exact (pcl3_frame_field E W m sp0 regs cs lo hi wlo whi (-24) 9%nat 9%bv HR Hsp
    (Hew 9%nat 9%bv eq_refl) I9).
- replace (sp0 - 64 + 48) with (sp0 + (-16)) by lia.
  exact (pcl3_frame_field E W m sp0 regs cs lo hi wlo whi (-16) 8%nat 8%bv HR Hsp
    (Hew 8%nat 8%bv eq_refl) I8).
- replace (sp0 - 64 + 56) with (sp0 + (-8)) by lia.
  exact (pcl3_frame_field E W m sp0 regs cs lo hi wlo whi (-8) 1%nat 1%bv HR Hsp
    (Hew 1%nat 1%bv eq_refl) I1).
Qed.

(* a value kept under a change of reader outside its own bytes *)
Lemma pcl3_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk (a + Z.of_nat k)) by lia. exact (H k Hkn). Qed.

(* the reader depends on the address only through its 64-bit truncation *)
Lemma pcl3_view_wrap : forall (H : word -> bool) (m : word -> option byte) a,
aview SEGS H m a = aview SEGS H m (bv_unsigned (Z_to_bv 64 a)).
Proof. intros H m a. unfold aview, mbyte. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* the read-only bytes cross a run that writes only the frame: a read-only byte of the frame window would have
   to be absent from memory, and the entry's stack bytes are present *)
Lemma pcl3_rod_keep : forall (W : world SEGS) (mem memc : word -> option byte) (lo hi : Z),
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
6316032 <= lo ->
(forall a, lo <= a < hi -> apresent (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
   aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) memc).
Proof.
intros W mem memc lo hi HROD Hlo Hpres KEEP a Hro Ho He.
pose proof (HROD a Hro Ho He) as HR.
pose proof (pcl3_bv64 (Z_to_bv 64 a)) as Hb.
assert (Hout : ~ (lo <= bv_unsigned (Z_to_bv 64 a) < hi)).
{ intros Hin.
  assert (Hni : ~ in_img SEGS (bv_unsigned (Z_to_bv 64 a)))
    by (intros Himg; pose proof (pa_img_range (bv_unsigned (Z_to_bv 64 a)) Himg); lia).
  assert (HN : seg_rom SEGS (Z_to_bv 64 a) = None).
  { pose proof (seg_rom_none SEGS (bv_unsigned (Z_to_bv 64 a)) ltac:(lia) Hni) as H0.
    rewrite Z_to_bv_bv_unsigned in H0. exact H0. }
  rewrite HN in HR. cbn [option_map] in HR.
  apply (aview_some_of_apresent SEGS (w_H W) mem (bv_unsigned (Z_to_bv 64 a)) (Hpres _ Hin)).
  rewrite <- (pcl3_view_wrap (w_H W) mem a). exact HR. }
assert (KEQ : aview SEGS (w_H W) memc (bv_unsigned (Z_to_bv 64 a))
            = aview SEGS (w_H W) mem (bv_unsigned (Z_to_bv 64 a)))
  by (apply KEEP; [lia | exact Hout]).
rewrite (pcl3_view_wrap (w_H W) memc a), KEQ, <- (pcl3_view_wrap (w_H W) mem a). exact HR.
Qed.

(* a live block lies below the stack and holds no image byte *)
Lemma pcl3_blk_low : forall ly S (W : world SEGS) mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
~ in_img SEGS a /\ 4096 <= a < alloc_ceiling.
Proof.
intros ly S W mem md p n a HAR Hin Ha.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4096 & Hceilp & _).
split; [exact (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin Ha) | lia].
Qed.

(* the footprint of rec_calls_free on record.spill alone: its nargs word and the blocks it frees *)
Lemma pcl3_rcf_fp_inv : forall P a, inFP (rcf_fp A_REC_SPILL [P]) a ->
A_REC_SPILL + 4 <= a < A_REC_SPILL + 8 \/ exists p n, In (p, n) P /\ p <= a < p + req_size n.
Proof.
intros P a Ha. unfold rcf_fp in Ha. cbn [length seq map concat] in Ha. rewrite app_nil_r in Ha.
apply inFP_app in Ha as [Ha | Ha].
- left. apply inFP_cons in Ha as [Ha | Ha];
  [unfold CALL_SIZE, CALL_OFF_NARGS in Ha; cbn in Ha; lia | exact (False_ind _ (inFP_nil a Ha))].
- right. exact (inFP_ablocks_fp_inv P a Ha).
Qed.

Lemma pcl3_rcf_spares : forall P a, (forall p n, In (p, n) P -> 4096 <= p) ->
~ (A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) -> (forall p n, In (p, n) P -> ~ (p <= a < p + req_size n)) ->
fp_spares (rcf_fp A_REC_SPILL [P]) a.
Proof.
intros P a Hpos Hs Hb. apply fp_spares_closed.
- intros H0. unfold YI16.sink_open_fp in H0. apply in_fp_inFP in H0.
  destruct (pcl3_rcf_fp_inv P 0 H0) as [H | (p & n & Hin & Hr)]; [unfold A_REC_SPILL in H; lia|].
  pose proof (Hpos p n Hin). pose proof (req_size_pos n). lia.
- intros H. destruct (pcl3_rcf_fp_inv P a H) as [H' | (p & n & Hin & Hr)];
  [exact (Hs H') | exact (Hb p n Hin Hr)].
Qed.

(* a state with no regions, to walk the jump that follows the call of rec_calls_free *)
Lemma pcl3_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bxp [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc. split; [|apply Forall_nil].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I |].
split; [exact I | split; exact I].
Qed.

(* the register and region readers of the walk *)
Ltac pcl3_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

Ltac pcl3_region HS i HR :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ssx (restrict ?H ?msx) =>
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  pose proof (pcl3_region_nth E ssx (restrict H msx) i r HS ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem restrict mkst] in HR
| st_ok _ ?E ?ssx (restrict ?H ?msx) =>
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth (segs := SEGS) E ssx (restrict H msx) i r HS
    ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem restrict mkst] in HR
end.

(* the write windows of the entry segment: the frame and g_rec.ncalls *)
Ltac pcl3_winA Usp EGu' :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin; cbv beta;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu' in Hrr;
     first [left; lia | right; unfold OFF_NCALLS; lia]|]); destruct Hin.

(* every write of the entry segment is a byte of the frame, or of g_rec, which the footprint names *)
Ltac pcl3_awrA Usp EGu' :=
  awr_ok_tac; [exact Usp|];
  eapply awr_ok_cons_gen; [reflexivity | exact EGu' | | apply awr_ok_nil];
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
  apply pcl3_awr_grec; unfold A_G_REC, REC_SIZE, OFF_NCALLS in *; lia.

(* The entry segment, as a step that hands the state at 0x8cd2c to its continuation. *)
Lemma pcl_entry_seg : forall ly S (W : world SEGS) regs mem md ch R O Q pu uri
  (POST : world SEGS -> config -> Prop),
afn_pre SEGS B PINS_CLEAR_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 pu ->
arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
st_nev S + EV_PINS_CLEAR R <= EV_MAX ->
mo_ok MT S (XM_PINS_CLEAR MT R uri) ->
(* the continuation: the two arms of record() meet at 0x8cd2c *)
(forall lyc Sc (Wc : world SEGS) memc mdc k c (regsJ : bvmap 5 word),
   ajournal SEGS B PINS_CLEAR_STK (spZ regs) (pcl3_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
   pcl_at_join B ly S W mem R (l_spill Q) lyc Sc Wc memc c k ->
   pcl_slot_ok c ->
   spZ regsJ = spZ regs - PCL_FRAME ->
   getr regsJ 8 = w64 c -> getr regsJ 9 = w64 pu ->
   getr regsJ 19 = w64 A_G_REC -> getr regsJ 20 = w64 SB ->
   getr regsJ 3 = w64 (as_gp B) -> getr regsJ 4 = w64 (as_tp B) ->
   (forall r, 22 <= r <= 27 -> getr regsJ (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
   pcl_frame_at (rdW Wc memc) (spZ regsJ) (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8))
     (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19))
     (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21)) ->
   mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
   blocks_bytes Sc <= blocks_bytes S ->
   SRr SEGS Wc (cfg_at SEGS (BASE + PCL_JOIN) regsJ memc mdc) POST) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_pins_clear) regs mem md) POST.
Proof.
intros ly S W regs mem md ch R O Q pu uri POST PRE HROD H10 HREP HO HEV HMOK K.
pose proof PRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof pa_base_lo as HBLO.
assert (WS : PINS_CLEAR_STK = 16560) by (vm_compute; reflexivity).
assert (WR : REC_CALLS_FREE_STK = 16496) by (vm_compute; reflexivity).
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328. lia. }
pose proof HREP as (Hgr8 & Hsc8 & Hapart & HG1 & HANS & HRPL & HSCAL & HOWN).
pose proof HG1 as (Hlen16 & HlenQ & HNC & HCALLS & HSPILL & HSPMAX).
pose proof HSPILL as (_ & HSP6 & HLP & _ & HSPN & HSPND & HSPA).
(* the entry state: the frame, the two shadow-base words and g_rec.ncalls; no shadow entry yet *)
pose proof (pcl_seed_entry B TL VOBJS cmd_prog_writable ly S W mem md regs
  (Z.of_nat (length (r_calls R))) HAR Hsp46 Hsp16
  ltac:(intros a Ha; apply Hpres; unfold PCL_FRAME in Ha; lia) ltac:(lia) HNC) as HS.
assert (SHOK : sh_ok SEGS Bxp [] (Eimg (Ereg regs (pcl_extra_e (Z.of_nat (length (r_calls R))))))
  (mrestrict (w_H W) mem)) by apply Forall_nil.
set (E := Eimg (Ereg regs (pcl_extra_e (Z.of_nat (length (r_calls R)))))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. unfold E.
  rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 rr) as Hr5;
    change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hm. }
assert (E32 : ew E PCL_SB = Z_to_bv 64 SB).
{ unfold E, PCL_SB. change 32%nat with (32 + 0)%nat.
  rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E33 : ew E PCL_N = Z_to_bv 64 (Z.of_nat (length (r_calls R)))).
{ unfold E, PCL_N. change 33%nat with (32 + 1)%nat.
  rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
assert (EG : ew E PCL_GR = Z_to_bv 64 A_G_REC).
{ rewrite (img_env_atomP E PCL_GR HEI ltac:(unfold PCL_GR, A_OBJ, A_TEXT, A_LIM; lia)),
    (pcl_grec_val VOBJS). reflexivity. }
assert (ESP : ew E PCL_SP = Z_to_bv 64 A_REC_SPILL).
{ rewrite (img_env_atomP E PCL_SP HEI ltac:(unfold PCL_SP, A_OBJ, A_TEXT, A_LIM; lia)),
    (pcl_spill_val VOBJS). reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (EGu : bv_unsigned (ew E PCL_GR) = A_G_REC)
  by (rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (EGu' : bv_unsigned (ew E 285) = A_G_REC) by exact EGu.
assert (E33' : ew E 33 = Z_to_bv 64 (Z.of_nat (length (r_calls R)))) by exact E33.
pose proof (ajournal_init SEGS B PINS_CLEAR_STK (pcl3_FP O) ly S W regs mem md ch PRE) as HJ.
unfold cfg_at, w64.
(* 0x8ccb4 .. 0x8ccf4: the frame, the shadow base, g_rec and its call count *)
paj_run_to_tok RUNTO HS HJ SHOK PCL_SPAN PCL_BR.
{ pcl3_awrA Usp EGu'. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv1 := mdx) in *; clearbody mdv1 end.
assert (WIN : forall b wlo whi a, In (b, wlo, whi) (windows pcl_rs_e) ->
  base_val E b + wlo <= a < base_val E b + whi ->
  spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4).
{ pcl3_winA Usp EGu'. }
(* 0x8ccf4: the test of the call count against 16 *)
psrr_branch_tok RUN BR HS SHOK PCL_SPAN.
- (* the table arm: fewer than 16 calls, the slot is g_rec.calls[ncalls] *)
  assert (Hn16 : (length (r_calls R) < 16)%nat).
  { rewrite branch_ne_U, (U_atom E 33 _ E33') in Hc by lia.
    rewrite U_SLit, (pcl3_zcanon 16) in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK PCL_SPAN PCL_JOIN.
  { pcl3_awrA Usp EGu'. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
  pmkst HS.
  pcl3_reg HS (2%bv : bv 5) Q2. pcl3_reg HS (3%bv : bv 5) Q3. pcl3_reg HS (4%bv : bv 5) Q4.
  pcl3_reg HS (8%bv : bv 5) Q8. pcl3_reg HS (9%bv : bv 5) Q9. pcl3_reg HS (19%bv : bv 5) Q19.
  pcl3_reg HS (20%bv : bv 5) Q20.
  pcl3_region HS 0%nat HRs. pcl3_region HS 3%nat HRn.
  assert (Q2' : getr (ms_regs ms0) 2 = w64 (spZ regs - 64)).
  { rewrite Q2. apply pcl3_denot_U. rewrite U_SOff, Usp. apply pcl3_zcanon. lia. }
  assert (Q3' : getr (ms_regs ms0) 3 = w64 (as_gp B))
    by (rewrite Q3, pcl3_soff0, (EEo 3%nat 3%bv eq_refl); exact Hgp).
  assert (Q4' : getr (ms_regs ms0) 4 = w64 (as_tp B))
    by (rewrite Q4, pcl3_soff0, (EEo 4%nat 4%bv eq_refl); exact Htp).
  assert (Q9' : getr (ms_regs ms0) 9 = w64 pu)
    by (rewrite Q9, pcl3_soff0, (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (Q19' : getr (ms_regs ms0) 19 = w64 A_G_REC) by (rewrite Q19, pcl3_soff0; exact EG).
  assert (Q20' : getr (ms_regs ms0) 20 = w64 SB) by (rewrite Q20, pcl3_soff0; exact E32).
  assert (Q8' : getr (ms_regs ms0) 8
    = w64 (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))))
    by (rewrite Q8; exact (pcl3_denot_slot E (Z.of_nat (length (r_calls R))) E33 ltac:(lia) EG)).
  assert (Hspj : spZ (ms_regs ms0) = spZ regs - PCL_FRAME).
  { unfold spZ at 1. rewrite Q2'. unfold w64, PCL_FRAME.
    rewrite unsigned_lit_small by lia. reflexivity. }
  (* the prologue and the store of ncalls + 1 are the only writes *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha H1 H2.
    rewrite (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms) (ms_mem ms0)
      (fun x => spZ regs - 64 <= x < spZ regs \/ A_G_REC + OFF_NCALLS <= x < A_G_REC + OFF_NCALLS + 4)
      HFr0); [ | pcl3_winA Usp EGu' | exact Ha | tauto].
    exact (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms) _ HFr WIN a Ha ltac:(tauto)). }
  assert (HNC1 : aval_mem (aview SEGS (w_H W) (ms_mem ms0)) (A_G_REC + OFF_NCALLS) 4
    (Z.of_nat (length (r_calls R)) + 1)).
  { apply (aval_mem_view SEGS). change 4%nat with (N.to_nat 4).
    apply (field_of_region E (mrestrict (w_H W) (ms_mem ms0)) PCL_GR A_G_REC _ _ _ _ _ 8 4
      (SOff 33 1) _ HRn EGu' ltac:(cbn [In]; tauto)); [| cbn; lia | cbn; lia].
    apply pcl3_denot_U. rewrite U_SOff, E33', unsigned_lit_small by lia. apply pcl3_zcanon. lia. }
  apply (K ly S W (ms_mem ms0) mdv2 0
    (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) (ms_regs ms0)).
  + exact HJ.
  + left. split; [exact Hn16|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact HNC1|]. split.
    { intros a Ha Hn. apply KEEP; [pose proof (pa_img_range a (cmd_prog_img a (recb_grec_in a Ha)));
        unfold A_G_REC, REC_SIZE in *; lia | unfold A_G_REC, REC_SIZE in *; lia | exact Hn]. }
    split.
    { intros a Ha. apply KEEP;
      [ unfold A_REC_SPILL, SC_SIZE in *; lia
      | unfold A_REC_SPILL, SC_SIZE in *; lia
      | unfold A_G_REC, A_REC_SPILL, SC_SIZE, OFF_NCALLS in *; lia ]. }
    intros q nn i Hin Hi.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q nn HAR Hin) as (_ & _ & _ & _ & _ & _ & Hnn0).
    pose proof (req_size_pos nn ltac:(lia)) as [_ Hrq].
    destruct (pcl3_blk_low ly S W mem md q nn (q + i) HAR Hin ltac:(lia)) as [Hni Hlo].
    apply KEEP; [lia | lia |].
    intros Hcc. apply Hni. apply cmd_prog_img, recb_grec_in.
    unfold A_G_REC, REC_SIZE, OFF_NCALLS in *. lia.
  + left. exists (Z.of_nat (length (r_calls R))).
    split; [unfold REC_CALLS_MAX; lia | reflexivity].
  + exact Hspj.
  + exact Q8'. + exact Q9'. + exact Q19'. + exact Q20'. + exact Q3'. + exact Q4'.
  + intros r Hr. assert (Hr6 : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    (match goal with |- getr _ ?rr = _ => pcl3_reg HS rr Qr end;
     rewrite Qr, pcl3_soff0; apply EEo; reflexivity).
  + rewrite Hspj.
    exact (pcl3_frame_of_region E W (ms_mem ms0) (spZ regs) regs _ _ _ _ _ HRs Usp EEo
      ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)
      ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)).
  + assert (Hsf0 : rec_spill_frees R = 0).
    { unfold rec_spill_frees. pose proof Hn16 as Hn'. apply Nat.ltb_lt in Hn'. rewrite Hn'. reflexivity. }
    rewrite Hsf0, Z.mul_0_l. exact (mle_start MT S MTL).
  + lia.
- (* the spill arm: the table holds 16 calls, record() frees the spill's arguments *)
  assert (Hn16 : length (r_calls R) = 16%nat).
  { rewrite branch_ne_U, (U_atom E 33 _ E33') in Hc by lia.
    rewrite U_SLit, (pcl3_zcanon 16) in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  paj_run_tok RUN HS HJ SHOK PCL_SPAN.
  { pcl3_awrA Usp EGu'. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
  pmkst HS.
  pcl3_reg HS (1%bv : bv 5) Q1. pcl3_reg HS (2%bv : bv 5) Q2. pcl3_reg HS (3%bv : bv 5) Q3.
  pcl3_reg HS (4%bv : bv 5) Q4. pcl3_reg HS (8%bv : bv 5) Q8. pcl3_reg HS (9%bv : bv 5) Q9.
  pcl3_reg HS (10%bv : bv 5) Q10. pcl3_reg HS (11%bv : bv 5) Q11.
  pcl3_reg HS (19%bv : bv 5) Q19. pcl3_reg HS (20%bv : bv 5) Q20.
  pcl3_region HS 0%nat HRs. pcl3_region HS 3%nat HRn.
  assert (Q2' : getr (ms_regs ms0) 2 = w64 (spZ regs - 64)).
  { rewrite Q2. apply pcl3_denot_U. rewrite U_SOff, Usp. apply pcl3_zcanon. lia. }
  assert (Q3' : getr (ms_regs ms0) 3 = w64 (as_gp B))
    by (rewrite Q3, pcl3_soff0, (EEo 3%nat 3%bv eq_refl); exact Hgp).
  assert (Q4' : getr (ms_regs ms0) 4 = w64 (as_tp B))
    by (rewrite Q4, pcl3_soff0, (EEo 4%nat 4%bv eq_refl); exact Htp).
  assert (Q8' : getr (ms_regs ms0) 8 = w64 A_REC_SPILL) by (rewrite Q8, pcl3_soff0; exact ESP).
  assert (Q9' : getr (ms_regs ms0) 9 = w64 pu)
    by (rewrite Q9, pcl3_soff0, (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (Q10' : getr (ms_regs ms0) 10 = w64 A_REC_SPILL) by (rewrite Q10, pcl3_soff0; exact ESP).
  assert (Q11' : getr (ms_regs ms0) 11 = w64 (Z.of_nat (length [l_spill Q])))
    by (rewrite Q11; reflexivity).
  assert (Q19' : getr (ms_regs ms0) 19 = w64 A_G_REC) by (rewrite Q19, pcl3_soff0; exact EG).
  assert (Q20' : getr (ms_regs ms0) 20 = w64 SB) by (rewrite Q20, pcl3_soff0; exact E32).
  assert (Qhi : forall r, 22 <= r <= 27 ->
    getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. assert (Hr6 : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    (match goal with |- getr _ ?rr = _ => pcl3_reg HS rr Qr end;
     rewrite Qr, pcl3_soff0; apply EEo; reflexivity). }
  assert (HRA : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + PCL_RET_RCF))
    by (rewrite Q1; apply codeptr_val; exact HEI).
  assert (Hspj : spZ (ms_regs ms0) = spZ regs - PCL_FRAME).
  { unfold spZ at 1. rewrite Q2'. unfold w64, PCL_FRAME.
    rewrite unsigned_lit_small by lia. reflexivity. }
  (* the prologue is the only write before the call *)
  assert (HNCc : aval_mem (aview SEGS (w_H W) (ms_mem ms0)) (A_G_REC + OFF_NCALLS) 4
    (Z.of_nat (length (r_calls R)))).
  { apply (aval_mem_view SEGS). change 4%nat with (N.to_nat 4).
    apply (field_of_region E (mrestrict (w_H W) (ms_mem ms0)) PCL_GR A_G_REC _ _ _ _ _ 8 4
      (SOff PCL_N 0) _ HRn EGu' ltac:(cbn [In]; tauto)); [| cbn; lia | cbn; lia].
    rewrite pcl3_soff0. exact E33. }
  assert (KEEPw : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha H1 H2.
    rewrite (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms) (ms_mem ms0)
      (fun x => spZ regs - 64 <= x < spZ regs \/ A_G_REC + OFF_NCALLS <= x < A_G_REC + OFF_NCALLS + 4)
      HFr0); [ | pcl3_winA Usp EGu' | exact Ha | tauto].
    exact (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms) _ HFr WIN a Ha ltac:(tauto)). }
  assert (KEEPc : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha H1.
    destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS)) as [Hl | Hl];
      [|destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS + 4)) as [Hh | Hh]].
    - apply KEEPw; [exact Ha | exact H1 | lia].
    - replace a with ((A_G_REC + OFF_NCALLS) + Z.of_nat (Z.to_nat (a - (A_G_REC + OFF_NCALLS)))) by lia.
      rewrite (HNCc (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)),
              (HNC (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)). reflexivity.
    - apply KEEPw; [exact Ha | exact H1 | lia]. }
  assert (HRODc : arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) (ms_mem ms0)))
    by exact (pcl3_rod_keep W mem (ms_mem ms0) (spZ regs - 64) (spZ regs) HROD ltac:(lia)
      ltac:(intros a Ha; apply Hpres; lia) KEEPc).
  (* the stack above the entry sp is still present at the call: no footprint byte is on the stack *)
  assert (HOb : forall pn, In pn O -> In pn (ablocks B ly S))
    by (intros pn Hpn; exact (lay_blocks_in _ _ _ _ _ _ HREP pn (proj1 (HO pn) Hpn))).
  assert (HFPlo : forall a, inFP (pcl3_FP O) a -> a < alloc_ceiling).
  { intros a Hfp. unfold pcl3_FP in Hfp.
    apply inFP_cons in Hfp as [Ha | Hfp]; [unfold A_G_REC, REC_SIZE in *; lia|].
    apply inFP_cons in Hfp as [Ha | Hfp]; [unfold A_REC_SPILL, SC_SIZE in *; lia|].
    destruct (inFP_ablocks_fp_inv O a Hfp) as (q & nn & Hin & Hr).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q nn HAR (HOb _ Hin)) as (_ & _ & Hceil2 & _). lia. }
  (* the spill's blocks, as the recorder's representation holds them *)
  assert (HPin : forall pn, In pn (l_spill Q) -> In pn (ablocks B ly S))
    by exact (acall_at_in _ _ _ _ _ HSPILL).
  assert (HPpos : forall p nn, In (p, nn) (l_spill Q) -> 4096 <= p).
  { intros p nn Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p nn HAR (HPin _ Hin)) as (_ & H4096 & _). exact H4096. }
  assert (HPO : forall pn, In pn (l_spill Q) -> In pn O).
  { intros pn Hpn. apply HO. unfold lay_blocks.
    apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  assert (Hsf : rec_spill_frees R = Z.of_nat (length (l_spill Q)))
    by (unfold rec_spill_frees; rewrite Hn16, HLP; reflexivity).
  assert (HEVk : EV_REC_CALLS_FREE [l_spill Q] = Z.of_nat (length (l_spill Q)))
    by (unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r; reflexivity).
  assert (SIGr : SIG CS_rec_calls_free = BASE + AF_rec_calls_free).
  { rewrite (SIGP CS_rec_calls_free
      ltac:(cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]))).
    f_equal; vm_compute; reflexivity. }
  rewrite SIGr.
  (* 0x8ccf8: rec_calls_free(&record.spill, 1) *)
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W (ms_regs ms0) (ms_mem ms0) _ PINS_CLEAR_STK (spZ regs)
      (pcl3_FP O) ly S W mem md [] ly S _ 0 REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q])
      (EV_REC_CALLS_FREE [l_spill Q]) (-64) (getr (ms_regs ms0) 1) [] _ HJ);
    [ rewrite Hspj; unfold PCL_FRAME; lia
    | reflexivity | lia | vm_compute; congruence | vm_compute; congruence
    | exact Q3' | exact Q4' | reflexivity
    | rewrite HRA; apply ret_ok_codeptr_v; [vm_compute; split; congruence | reflexivity]
    | rewrite HRA, unsigned_lit_small by (unfold PCL_RET_RCF, AF_pins_clear; lia);
      unfold PCL_RET_RCF, AF_pins_clear; lia
    | apply achain_low; unfold s0Z; rewrite Q8'; unfold w64;
      rewrite unsigned_lit_small by (unfold A_REC_SPILL; lia); unfold A_REC_SPILL; lia
    | | | ].
    - intros HPRE1.
      assert (HT := TRCF fx ly S W (ms_regs ms0) (ms_mem ms0) mdv2 [] A_REC_SPILL [l_spill Q]
        HPRE1 HRODc Q10' Q11' ltac:(cbn [length]; lia)
        ltac:(right; left; unfold A_REC_SPILL, SC_SIZE, CALL_SIZE; cbn [length Z.of_nat]; lia)
        ltac:(unfold A_REC_SPILL; reflexivity)).
      unfold apost_base, cfg_at, w64 in HT. apply HT.
      + intros i P Hi. destruct i as [|i]; [|destruct i; discriminate Hi].
        cbn [nth_error] in Hi. injection Hi as <-.
        split; [lia|]. split.
        * cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r, HLP.
          apply (pcl3_aval_kept (aview SEGS (w_H W) mem)); [exact HSPN|].
          intros x Hx. apply KEEPc; unfold A_REC_SPILL, CALL_OFF_NARGS in *; cbn [Z.of_nat] in *; lia.
        * intros a pn Ha.
          assert (Hab : (a < length (l_spill Q))%nat)
            by (apply nth_error_Some; rewrite Ha; discriminate).
          destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Hs.
          -- destruct (HSPA a s pn Hs Ha) as (G1 & _ & G3 & _). split; [|exact G3].
             cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
             apply (pcl3_aval_kept (aview SEGS (w_H W) mem)); [exact G1|].
             intros x Hx. apply KEEPc;
               unfold A_REC_SPILL, CALL_OFF_ARGS in *; cbn [Z.of_nat] in *; lia.
          -- exfalso. apply nth_error_None in Hs. lia.
      + cbn [concat]. rewrite app_nil_r. exact HSPND.
      + rewrite HEVk, <- Hsf.
        assert (HEVle : rec_spill_frees R <= EV_PINS_CLEAR R)
          by (cbv [EV_PINS_CLEAR xstrdup_c.EV_XSTRDUP answer_code_c.EV_ANSWER_CODE
                   hand_back_c.EV_HAND_BACK]; lia).
        lia.
      + apply (mo_ok_le MT MTL S _ (XM_PINS_CLEAR MT R uri) HMOK).
        cbv [XM_REC_CALLS_FREE XM_PINS_CLEAR answer_code_c.XM_ANSWER_CODE
             hand_back_c.XM_HAND_BACK xstrdup_c.XM_XSTRDUP].
        cbn [concat]. rewrite app_nil_r, <- Hsf.
        pose proof (mo_free_nonneg MT MTL).
        pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg uri)) + 1) ltac:(lia)).
        pose proof (mo_malloc_nonneg MT MTL
          (Z.of_nat (length (resp (snd (pins_clear_m R uri)))) + 1) ltac:(lia)). lia.
    - intros a Ha. destruct (pcl3_rcf_fp_inv (l_spill Q) a Ha) as [Hs | (p & nn & Hin & Hr)].
      + apply pcl3_awr_spill. unfold A_REC_SPILL, SC_SIZE in *. lia.
      + right; left. split; [|exists p, nn; split; [exact (HPin _ Hin) | exact Hr]].
        unfold pcl3_FP. apply inFP_cons. right. apply inFP_cons. right.
        replace a with (p + (a - p)) by lia.
        apply (inFP_ablocks_fp O p nn (a - p)); [exact (HPO _ Hin) | lia].
    - intros ly3 S3 W3 regs3 mem3 md3 _ a Ha Hw _. exfalso.
      destruct (pcl3_rcf_fp_inv (l_spill Q) a Ha) as [Hs | (p & nn & Hin & Hr)];
        [unfold A_REC_SPILL in Hs; lia|].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p nn HAR (HPin _ Hin)) as (_ & _ & Hceil2 & _). lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJr & HP2 & HK2).
  destruct HK2 as (HPERM & HNARGS & _ & HBLKK & _ & _ & _ & HBB & HMLE).
  pose proof (proj1 HJr) as HAR2.
  pose proof HJr as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
  (* 0x8cd10: `j 0x8cd2c`, where the two arms meet *)
  rewrite HRA.
  destruct (pcl3_seed0 W2 regs2 mem2 PCL_RET_RCF) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 PCL_SPAN PCL_JOIN.
  { apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv3 := mdx) in *; clearbody mdv3 end.
  pmkst HS2.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha.
    apply (kept_of_frame (segs := SEGS) _ _ (w_H W2) mem2 (ms_mem ms1) (fun _ => False) HFr1);
      [| exact Ha | tauto].
    intros b wlo whi x Hin. destruct Hin. }
  assert (HAE2 : env_agree 32 (Ereg regs2 []) (Eimg (Ereg regs2 []))).
  { split; [intros nn Hnn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [] HS2 HAE2
    ltac:(vm_compute; reflexivity)) as HPT3.
  cbn [ms_regs restrict] in HPT3.
  assert (HPall : forall r, acallee_saved r ->
    getr (ms_regs ms1) (Z_to_bv 5 r) = getr (ms_regs ms0) (Z_to_bv 5 r))
    by exact (aregs_preserved_trans _ _ _ HP2 HPT3).
  (* the image bytes of g_rec and record.spill the call keeps *)
  assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> ~ (A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms0) a).
  { intros a Hi Ho He Hs. apply (G3 a Hi Ho He).
    apply pcl3_rcf_spares; [exact HPpos | exact Hs |].
    intros p nn Hin Hr. exact (proj1 (pcl3_blk_low ly S W mem md p nn a HAR (HPin _ Hin) Hr) Hi). }
  assert (KPG : forall a, Exists (in_zr a) recb_PG -> ~ (A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) ->
    aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
  { intros a HP Hs. destruct (recb_prog_unowned_m B HB cmd_prog_img a HP) as (Hi & Ho & He).
    pose proof (pa_img_range a Hi) as Har.
    rewrite KEEP3 by lia. rewrite (KIMG a Hi Ho He Hs). apply KEEPc; lia. }
  replace (0 + EV_REC_CALLS_FREE [l_spill Q]) with (Z.of_nat (length (l_spill Q))) in HJ2
    by (rewrite HEVk; lia).
  assert (P2 : getr (ms_regs ms1) 2 = getr (ms_regs ms0) 2)
    by exact (HPall 2 ltac:(unfold acallee_saved; lia)).
  assert (Hsp1 : spZ (ms_regs ms1) = spZ regs - PCL_FRAME)
    by (unfold spZ; rewrite P2; exact Hspj).
  apply (K ly2 S2 W2 (ms_mem ms1) mdv3 (Z.of_nat (length (l_spill Q))) A_REC_SPILL (ms_regs ms1)).
  + exact HJ2.
  + right. split; [exact Hn16|]. split; [reflexivity|]. split; [reflexivity|].
    split; [cbn [concat] in HPERM; rewrite app_nil_r in HPERM; exact HPERM|].
    split.
    { pose proof (HNARGS 0%nat ltac:(cbn [length]; lia)) as H0.
      cbn [Z.of_nat] in H0. rewrite Z.mul_0_r, Z.add_0_r in H0.
      apply (pcl3_aval_kept (aview SEGS (w_H W2) mem2)); [exact H0|].
      intros x Hx. apply KEEP3. unfold A_REC_SPILL, CALL_OFF_NARGS in *; cbn [Z.of_nat] in *; lia. }
    split.
    { intros a Ha. apply KPG; [apply recb_grec_in; exact Ha|].
      unfold A_G_REC, A_REC_SPILL, REC_SIZE in *. lia. }
    split.
    { intros a Ha Hn. apply KPG; [apply recb_spill_in; exact Ha|].
      unfold CALL_OFF_NARGS in Hn. lia. }
    intros p nn i Hin Hi.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p nn HAR2 Hin) as (_ & H4096 & Hceil2 & _ & _ & _ & Hnn0).
    pose proof (req_size_pos nn ltac:(lia)) as [_ Hrq].
    rewrite KEEP3 by lia. rewrite (HBLKK p nn i Hin Hi). apply KEEPc; lia.
  + right. reflexivity.
  + exact Hsp1.
  + etransitivity; [exact (HPall 8 ltac:(unfold acallee_saved; lia)) | exact Q8'].
  + etransitivity; [exact (HPall 9 ltac:(unfold acallee_saved; lia)) | exact Q9'].
  + etransitivity; [exact (HPall 19 ltac:(unfold acallee_saved; lia)) | exact Q19'].
  + etransitivity; [exact (HPall 20 ltac:(unfold acallee_saved; lia)) | exact Q20'].
  + etransitivity; [exact (HPall 3 ltac:(unfold acallee_saved; lia)) | exact Q3'].
  + etransitivity; [exact (HPall 4 ltac:(unfold acallee_saved; lia)) | exact Q4'].
  + intros r Hr.
    etransitivity; [exact (HPall r ltac:(unfold acallee_saved; lia)) | exact (Qhi r Hr)].
  + assert (HFRc : pcl_frame_at (aview SEGS (w_H W) (ms_mem ms0)) (spZ regs - PCL_FRAME)
      (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
      (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))
      (bv_unsigned (getr regs 21)))
      by exact (pcl3_frame_of_region E W (ms_mem ms0) (spZ regs) regs _ _ _ _ _ HRs Usp EEo
        ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)
        ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto) ltac:(cbn [In]; tauto)).
    assert (KFR : forall x, spZ regs - 64 <= x < spZ regs ->
      aview SEGS (w_H W2) (ms_mem ms1) x = aview SEGS (w_H W) (ms_mem ms0) x).
    { intros x Hx. rewrite KEEP3 by lia. apply G1; [lia | lia |].
      intros Hf. destruct (pcl3_rcf_fp_inv (l_spill Q) x Hf) as [Hs | (p & nn & Hin & Hr)];
        [unfold A_REC_SPILL in Hs; lia|].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p nn HAR (HPin _ Hin)) as (_ & _ & Hceil2 & _). lia. }
    rewrite Hsp1.
    unfold pcl_frame_at in HFRc |- *. unfold PCL_FRAME in *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat apply conj; try assumption;
      (apply (pcl3_aval_kept (aview SEGS (w_H W) (ms_mem ms0))); [assumption|];
       intros x Hx; apply KFR; cbn [Z.of_nat] in *; lia).
  + rewrite Hsf. unfold XM_REC_CALLS_FREE in HMLE. cbn [concat] in HMLE.
    rewrite app_nil_r in HMLE. exact HMLE.
  + unfold LIVE_REC_CALLS_FREE in HBB. lia.
Qed.
End e.
End f.
End d.
