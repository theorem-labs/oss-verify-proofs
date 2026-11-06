(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the last step of segment S01 (lib/A/Prog/verbs_receive_s01.v) of the walk of
   verbs_receive on the ASan build of plugin-hostd/fuzz_command: from what the walk knows at 0x8d5c4 (the journal
   from the entry, the frame's flag word and shadow, the registers, the saves and the spill slot, and that the
   program's statics and the live blocks still hold the entry's bytes) it builds vr_core of lib/A/Prog/verbs_receive_iface.v
   at vr_b1's arguments. The read-only bytes are carried by the journal (the walk's footprint holds none of them,
   as the S20 kit's aro_kept, in an earlier version of lib/A/Prog/verbs_receive_s20_k.v, :222). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16 YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the 128 shadow bytes of the side-stack frame after the prologue, by position *)
Definition vr01_shv (i : nat) : Z :=
if (i <? 4)%nat then 0xf1 else if (i <? 68)%nat then 0xf8 else if (i <? 76)%nat then 0xf2
else if (i =? 76)%nat then 0xf8 else if (i <? 80)%nat then 0xf3 else 0.
Lemma vr01_sh1_nth : forall i, (i < 128)%nat -> nth i vr_sh1 0 = vr01_shv i.
Proof. intros i Hi. do 128 (destruct i as [|i]; [reflexivity|]). lia. Qed.
Lemma vr01_shv_mid : forall i, (4 <= i < 68)%nat -> vr01_shv i = 0xf8.
Proof.
intros i Hi. unfold vr01_shv. destruct (i <? 4)%nat eqn:E1; [apply Nat.ltb_lt in E1; lia|].
destruct (i <? 68)%nat eqn:E2; [reflexivity | apply Nat.ltb_ge in E2; lia].
Qed.
Lemma vr01_shv_hi : forall i, (80 <= i)%nat -> vr01_shv i = 0.
Proof.
intros i Hi. unfold vr01_shv.
destruct (i <? 4)%nat eqn:E1; [apply Nat.ltb_lt in E1; lia|]. destruct (i <? 68)%nat eqn:E2; [apply Nat.ltb_lt in E2; lia|].
destruct (i <? 76)%nat eqn:E3; [apply Nat.ltb_lt in E3; lia|]. destruct (i =? 76)%nat eqn:E4; [apply Nat.eqb_eq in E4; lia|].
destruct (i <? 80)%nat eqn:E5; [apply Nat.ltb_lt in E5; lia | reflexivity].
Qed.

(* the bytes the walk's stores must not reach: the program's statics and the live blocks of a state *)
Definition vr01_keep (B : asyms) (ly : alayout) (S : astate) (a : Z) : Prop :=
inFP cmd_PG a \/ (exists p m, In (p, m) (ablocks B ly S) /\ p <= a < p + req_size m).

Lemma vr01_aval_of_val_mem : forall segs H (m : word -> option byte) a n v, val_mem segs (mrestrict H m) a n v ->
aval_mem (aview segs H m) a n v.
Proof.
intros segs H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. cbv [YO0f.le_byte YG0f.le_byte]. apply Z.mod_mod. lia.
Qed.

(* a one-byte literal chunk and an eight-byte chunk of a region of a symbolic state, as views *)
Lemma vr01_region_byte : forall segs E (H : word -> bool) m n lo hi wlo whi cs b od z v,
region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 (SLit z))) cs ->
bv_unsigned (sv_denot E (SLit z)) mod 256 = v ->
aview segs H m (b + od) = Some v.
Proof.
intros segs E H m n lo hi wlo whi cs b od z v HR Hb Hin Hv.
pose proof (field_of_region_any (segs := segs) E (mrestrict H m) n b cs lo hi wlo whi od 1 (SLit z) HR Hb Hin ltac:(lia)) as Hm.
pose proof (vr01_aval_of_val_mem segs H m _ _ _ Hm 0%nat ltac:(cbn; lia)) as H0.
rewrite Z.add_0_r in H0. rewrite H0. f_equal. rewrite <- Hv.
cbv [YG0f.le_byte]. change (8 * Z.of_nat (N.to_nat 1)) with 8. change (8 * Z.of_N 1) with 8.
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma vr01_region_word : forall segs E (H : word -> bool) m n lo hi wlo whi cs b od e,
region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 8 e)) cs ->
aval_mem (aview segs H m) (b + od) 8 (bv_unsigned (sv_denot E e)).
Proof.
intros segs E H m n lo hi wlo whi cs b od e HR Hb Hin.
pose proof (field_of_region_any (segs := segs) E (mrestrict H m) n b cs lo hi wlo whi od 8 e HR Hb Hin ltac:(lia)) as Hm.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Hm.
rewrite Z.mod_small in Hm by (pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
exact (vr01_aval_of_val_mem segs H m _ _ _ Hm).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the program's statics and the live blocks lie below the allocation ceiling, apart from the side-stack frame
   (class 4) and its shadow *)
Lemma vr01_keep_apart : forall ly S (W : world SEGS) mem md pos a, AR SEGS B ly S W mem md -> In (4, pos) (frames S) ->
vr01_keep B ly S a ->
0 <= a < alloc_ceiling /\ ~ (frame_addr ly 4 pos <= a < frame_addr ly 4 pos + 1024) /\
~ (shadow_addr (frame_addr ly 4 pos) <= a < shadow_addr (frame_addr ly 4 pos) + 128).
Proof.
intros ly S W mem md pos a HAR Hin Hk.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly S W mem md 4 pos HAR Hin) as (HF4 & HFc & HFapp).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite HFB in HFc, HFapp.
assert (HsF : shadow_addr (frame_addr ly 4 pos) = 2147450880 + frame_addr ly 4 pos / 8) by reflexivity.
rewrite HsF. clear HsF.
destruct Hk as [Hk | (p & m & Hpm & Hk)].
- destruct (PROGU a Hk) as (Hi & _ & _). pose proof (pa_img_range a Hi) as Hir.
  split; [lia|]. split; [|lia].
  intros Hr. apply (frm_img SEGS B LAWS ly S W mem md 4 pos a HAR Hin); [rewrite HFB; exact Hr | exact Hi].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hpm) as (_ & Hp4 & Hpc & Happ & _).
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md p m 4 pos HAR Hpm Hin) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFB in D.
  split; [lia|]. split; [lia|].
  intros Hr. exact (fshadow_not_app (frame_addr ly 4 pos) 128 p (req_size m) a HF4 ltac:(lia) Happ Hr Hk).
Qed.

Lemma vr01_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof. intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]. Qed.

(* the S20 kit's aro_kept: a footprint without read-only bytes and without the sink token keeps them *)
Lemma vr01_aro_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
(forall a, in_roP SEGS RLO RHI a -> ~ inFP FP a) -> ~ YI16.sink_open_fp FP ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HFP Hso HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a (vr01_ro_img a Hro) Ho He (fp_spares_closed FP a Hso (HFP a Hro))). exact (HR a Hro Ho He).
Qed.

(* the walk's footprint (the program's statics and the recorder's blocks) holds no read-only byte and not the
   sink token *)
Lemma vr01_fp_ok : forall e ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
(forall pn, In pn (e_O e) -> In pn (ablocks B ly S)) ->
(forall a, in_roP SEGS RLO RHI a -> ~ inFP (vr_fp e) a) /\ ~ YI16.sink_open_fp (vr_fp e).
Proof.
intros e ly S W mem md HAR HO. split.
- intros a Hro (r & Hr & Ha). unfold vr_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  + apply (RPG a); [|exact Hro]. exists r. split; [|exact Ha]. change cmd_PG with VERBS_RECEIVE_PG. exact Hr.
  + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p m] & <- & Hpm). cbn [fst snd] in Ha.
    exact (blk_img SEGS B LAWS _ _ _ _ _ p m a HAR (HO _ Hpm) ltac:(lia) (vr01_ro_img a Hro)).
- intros (r & Hr & Ha). unfold vr_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  + unfold VERBS_RECEIVE_PG, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
  + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p m] & <- & Hpm). cbn [fst snd] in Ha.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR (HO _ Hpm)) as (_ & Hp4 & _). lia.
Qed.

(* the four GOT words the recorder reads are read-only bytes of the image (the S20 kit's cmd_got_of_ro) *)
Lemma vr01_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [H _]. unfold cmd_ro_bytes in H.
repeat lazymatch type of H with
| abytes_atR _ _ RO_ptr_a7068 /\ _ => fail
| _ /\ _ => apply proj2 in H
end.
destruct H as (H1 & H2 & H3 & H4).
unfold cmd_got_ok, aval_mem.
split; [|split; [|split]]; intros k Hk;
[rewrite (H1 k) | rewrite (H2 k) | rewrite (H3 k) | rewrite (H4 k)]; try (cbn; lia);
do 8 (destruct k as [|k]; [reflexivity|]); lia.
Qed.

Lemma vr01_env_of : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> vr_env B W mem.
Proof.
intros ly S W mem md HAR Haro. pose proof (ROA ly S W mem md HAR Haro) as Hro.
destruct (RECC ly S W mem md HAR) as (Hf & Hg & He).
split; [exact Haro|]. split; [exact (vr01_got_of_ro _ Hro)|]. split; [exact Hro|]. split; [exact Hg|]. split; [exact Hf | exact He].
Qed.

(* vr_core at vr_b1's arguments *)
Lemma vr01_final : forall e pos F S2 f regsf memf mdf,
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] (e_ly e) S2 (e_W e) memf mdf 0 ->
S2 = set_fs f (e_S e) ->
F = frame_addr (e_ly e) 4 pos ->
rdword (rdW (e_W e) memf) (F + 1016) = Some (flag_addr (e_ly e) 4 pos) ->
(forall i, (i < 128)%nat -> rdW (e_W e) memf (shadow_addr F + Z.of_nat i) = Some (vr01_shv i)) ->
vr_rv regsf (vr_base B e ++ vr_rl1 e F) ->
vr_saved e (e_W e) memf ->
vr_spill e (e_W e) memf (vr_sl1 F) ->
(forall a, vr01_keep B (e_ly e) (e_S e) a -> rdW (e_W e) memf a = rdW (e_W e) (e_mem e) a) ->
vr_core B MT e pos F [] vr_sh1 (vr_sl1 F) (vr_rl1 e F) (e_R e) (e_O e) (e_q0 e) 0 0 0 0
  (e_ly e) S2 (e_W e) regsf memf mdf.
Proof.
intros e pos F S2 f regsf memf mdf HE HJ ES2 EF HFL HSH HRV HSAV HSPL HK.
unfold vr_ent in HE. cbv zeta in HE.
destruct HE as (HPRE & HROD & _ & _ & _ & _ & _ & _ & _ & _ & HnO & _ & _ & HREP & _ & _ & _ & _ & _ & HPERM & HQ0 & _).
pose proof (proj1 HJ) as HARf. pose proof (proj1 HPRE) as HAR0.
assert (Eab : ablocks B (e_ly e) S2 = ablocks B (e_ly e) (e_S e)) by (rewrite ES2; reflexivity).
assert (HO0 : forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e)))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ HREP Hpn)).
destruct (vr01_fp_ok e _ _ _ _ _ HAR0 HO0) as [HFPro HFPs].
split; [exact HJ|]. split; [lia|].
split.
{ exists 0. split; [lia|]. split; [lia|]. split; [lia|]. rewrite ES2. apply (mo_le_set_fs_r MT MTFL).
  apply (mo_le_mono MT MTL _ _ 0); [exact (mo_le_refl MT MTL _) | lia]. }
split; [lia|].
split.
{ split; [exact EF|]. split; [exact HFL|]. intros i Hi. rewrite (vr01_sh1_nth i Hi). exact (HSH i Hi). }
split; [exact HRV|]. split; [exact HSAV|]. split; [exact HSPL|].
split; [exact (vr01_env_of _ _ _ _ _ HARf (vr01_aro_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HFPro HFPs HROD))|].
split.
{ apply (rec_repA_agree B _ _ _ _ _ _ _ _ HREP).
  - intros pn _ Hpn. rewrite Eab. exact Hpn.
  - intros k Hk. apply HK. left. exists (A_G_REC, A_G_REC + 960).
    split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Hk; lia].
  - intros k Hk. apply HK. left. exists (A_REC_SPILL, A_REC_SPILL + 56).
    split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Hk; lia].
  - intros [p m] Hpn k Hk. cbn [fst snd] in Hk |- *. apply HK. right. exists p, m. split; [exact (HO0 _ Hpn)|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR0 (HO0 _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m (proj1 Hm)). lia. }
split; [exact HnO|].
split; [rewrite Eab; exact HPERM|].
apply (aval_mem_agree _ _ _ 4 _ HQ0). intros k Hk. apply HK. left. exists (A_G_QUITTING, A_G_QUITTING + 4).
split; [right; right; left; reflexivity | cbn [fst snd]; lia].
Qed.
End e.
End f.
End d.

