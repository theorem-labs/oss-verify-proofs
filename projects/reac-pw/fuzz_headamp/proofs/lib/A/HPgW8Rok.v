(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Rok.v at 888d1ffb4c3; module paths fuzz_role -> fuzz_headamp, RPgBase / RPgCSpec / RPgImgA / RPgMem / RPgSeg -> HPgBase / HPgCSpec / HPgImgA / HPgMem / HPgSeg, the rl_ / rm_ / rs_ prefixes -> hd_ / hm_ / hs_; class-4 frame (1024 bytes, 128 shadow bytes); the ten real-frame cells by headamp's frame-slot map (R+0x60 .. R+0xf0 -> R+0x88 .. R+0x110, bound R+0xf8 -> R+0x118). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW8Kit HPgW8BlkA HPgW8BlkB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

Lemma wF_zone : forall F, F mod 32 = 0 -> in_app F 1024 -> F + 1024 <= alloc_ceiling ->
  4096 <= F /\ 0x7fff8000 <= shadow_addr F /\ shadow_addr F + 128 <= 0x10007fff8000 /\
  (F + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= F) /\ F = 8 * (F / 8) /\ shadow_addr F = 0x7fff8000 + F / 8.
Proof.
intros F H32 Happ Hhi. pose proof YM05.alloc_ceiling_val as Hceil.
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ. destruct Happ as [Hlo Hz].
assert (HF8 : F mod 8 = 0).
{ apply Z.mod_divide in H32; [|lia]. destruct H32 as [q ->]. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite HF8, Z.add_0_r in D.
unfold shadow_addr, SHADOW_OFF.
split; [lia|]. split; [lia|]. split; [lia|]. split; [destruct Hz as [Hz|[Hz1 Hz2]]; [left | right]; lia|].
split; [exact D | reflexivity].
Qed.

(* the 13 frame-shadow bytes of e, as a run's last state leaves them *)
Lemma w_fsh_out : forall E ss ms sF,
  st_ok rsegs E ss ms -> bv_unsigned (ew E 19) = sF ->
  In (YP09.mkRegion (Some 19%nat) 30 43 30 43
     (map (fun o => YP09.mkChunk o (CVal 1 (SLit 18446744073709551608))) [42; 41; 40; 39; 38; 33; 32; 31; 30; 37; 36; 35; 34])) (ss_mem ss) ->
  forall o, 30 <= o < 43 -> mbyte rsegs (ms_mem ms) (sF + o) = Some (Z_to_bv 8 248).
Proof.
intros E ss ms sF HS H19 Hin o Ho.
assert (Hc : In (YP09.mkChunk o (CVal 1 (SLit 18446744073709551608)))
  (map (fun o => YP09.mkChunk o (CVal 1 (SLit 18446744073709551608))) [42; 41; 40; 39; 38; 33; 32; 31; 30; 37; 36; 35; 34])).
{ apply in_map_iff. exists o. split; [reflexivity|]. cbn [In]. lia. }
pose proof (w_chunk_of E ss ms _ _ HS Hin Hc) as C. apply w_chunk1 in C. cbn [YP09.r_base base_val] in C. rewrite H19 in C.
rewrite C. f_equal. rewrite U_SLit. apply bv_eq. vm_compute. reflexivity.
Qed.

(* ============================== the region proofs of the entry states ============================== *)
Lemma rok_slots : forall E (H : word -> bool) mem R F pp fs kk cnt,
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 27) = pp -> bv_unsigned (ew E A_F) = F ->
  bv_unsigned (ew E A_FS) = fs -> bv_unsigned (ew E A_KK) = kk -> bv_unsigned (ew E A_CNT) = cnt ->
  Forall (fun c => val_mem rsegs (mrestrict H mem) (R + fst c) 8 (snd c mod 2 ^ 64)) (wslot_vals F pp fs kk cnt) ->
  0 <= R -> R + 0x118 <= 2 ^ 64 -> 0 <= pp -> pp + 0x4d14 < 2 ^ 64 ->
  region_ok rsegs E (mrestrict H mem) r_slots.
Proof.
intros E H mem R F pp fs kk cnt U9 U27 U32 U38 U39 U40 HSL HR1 HR2 Hp1 Hp2.
assert (HSLf : forall o v, In (o, v) (wslot_vals F pp fs kk cnt) ->
    val_mem rsegs (mrestrict H mem) (R + o) 8 (v mod 2 ^ 64))
    by (intros o v Hin; exact (proj1 (Forall_forall _ _) HSL (o, v) Hin)).
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val r_slots].
rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold wslot_chunks. repeat apply Forall_cons; [ | | | | | | | | | | apply Forall_nil].
- apply (wchunk8 E _ R 0x88 _ (pp + 0x4014)); [cbn [sv_denot]; rewrite U27; reflexivity | apply HSLf; cbn; tauto].
- apply (wchunk8 E _ R 0x90 _ (Z.shiftr (pp + 0x4d14) 3)); [| apply HSLf; cbn; tauto].
  rewrite denot_lit_U. f_equal. rewrite U_SAlu, U_SOff, U_SLit, U27. cbn [zalu_raw].
  change (Z.land (zcanon 3) 63) with 3. rewrite (zcanon_id (pp + 0x4d14)) by (unfold M64; lia).
  apply zcanon_id. rewrite Z.shiftr_div_pow2 by lia.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold M64; lia].
- apply (wchunk8 E _ R 0xa0 _ (pp + 0x4d14)); [cbn [sv_denot]; rewrite U27; reflexivity | apply HSLf; cbn; tauto].
- apply (wchunk8 E _ R 0xc8 _ cnt); [cbn [sv_denot]; rewrite U40, Z.add_0_r; reflexivity | apply HSLf; cbn; tauto].
- apply (wchunk8 E _ R 0xe0 _ (F + 0xf8)); [cbn [sv_denot]; rewrite U32; reflexivity | apply HSLf; cbn; tauto].
- apply (wchunk8 E _ R 0xe8 _ fs); [cbn [sv_denot]; rewrite U38, Z.add_0_r; reflexivity | apply HSLf; cbn; tauto].
- apply (wchunk8 E _ R 0xf8 _ kk); [cbn [sv_denot]; rewrite U39, Z.add_0_r; reflexivity | apply HSLf; cbn; tauto].
- apply (wchunk8 E _ R 0x100 _ (-0x4001)); [cbn [sv_denot]; unfold M2; apply wZ_to_bv_mod | apply HSLf; cbn; tauto].
- apply (wchunk8 E _ R 0x108 _ (-0x3ffd)); [cbn [sv_denot]; unfold M2; apply wZ_to_bv_mod | apply HSLf; cbn; tauto].
- apply (wchunk8 E _ R 0x110 _ (F + 0xf0)); [cbn [sv_denot]; rewrite U32; reflexivity | apply HSLf; cbn; tauto].
Qed.
Lemma rok_sh4 : forall E (H : word -> bool) mem pp,
  bv_unsigned (ew E 20) = shadow_addr pp + 2048 ->
  (forall i, 0 <= i < 2468 -> aview rsegs H mem (shadow_addr pp + i) = Some 0) ->
  0 <= shadow_addr pp -> shadow_addr pp + 2468 <= 2 ^ 64 ->
  region_ok rsegs E (mrestrict H mem) r_sh4.
Proof.
intros E H mem pp U20 HSH H1 H2. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val r_sh4].
rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; [ | | apply Forall_nil]; apply wchunk1z; rewrite <- Z.add_assoc; apply HSH; lia.
Qed.
Lemma rok_len : forall E (H : word -> bool) mem pp v lv,
  bv_unsigned (ew E 21) = pp + 0x4000 -> sv_denot E v = Z_to_bv 64 lv ->
  val_mem rsegs (mrestrict H mem) (pp + 0x4000) 8 lv -> 0 <= lv < 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> apresent H mem (pp + 0x4000 + i)) -> 0 <= pp -> pp + 0x4008 <= 2 ^ 64 ->
  region_ok rsegs E (mrestrict H mem) (r_lenv v).
Proof.
intros E H mem pp v lv U21 Hv HL Hlv HW H1 H2. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val r_lenv].
rewrite U21. split; [lia|]. split; [lia|].
split; [intros o Ho; apply apresent_writable, HW; lia|].
repeat apply Forall_cons; [ | apply Forall_nil].
apply (wchunk8 E _ (pp + 0x4000) 0 _ lv); [exact Hv|]. rewrite Z.add_0_r, Z.mod_small by lia. exact HL.
Qed.
Lemma rok_ne : forall E (H : word -> bool) mem pp ne,
  bv_unsigned (ew E 27) = pp -> bv_unsigned (ew E A_NE) = ne ->
  val_mem rsegs (mrestrict H mem) (pp + 0x4d14) 4 ne -> 0 <= ne < 2 ^ 32 ->
  (forall i, 0 <= i < 4 -> apresent H mem (pp + 0x4d14 + i)) -> 0 <= pp -> pp + 0x4d18 <= 2 ^ 64 ->
  region_ok rsegs E (mrestrict H mem) r_ne.
Proof.
intros E H mem pp ne U27 U41 HN Hne HW H1 H2. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val r_ne].
rewrite U27. split; [lia|]. split; [lia|].
split; [intros o Ho; replace (pp + o) with (pp + 0x4d14 + (o - 0x4d14)) by lia; apply apresent_writable, HW; lia|].
repeat apply Forall_cons; [ | apply Forall_nil].
apply (wchunk4 E _ pp 0x4d14 _ ne); [cbn [sv_denot]; rewrite U41, Z.add_0_r; reflexivity | lia | exact HN].
Qed.
Lemma rok_fsh : forall E (H : word -> bool) mem sF,
  bv_unsigned (ew E 19) = sF -> (forall o, 30 <= o < 43 -> apresent H mem (sF + o)) -> 0 <= sF -> sF + 43 <= 2 ^ 64 ->
  region_ok rsegs E (mrestrict H mem) r_fsh.
Proof.
intros E H mem sF U19 HW H1 H2. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val r_fsh].
rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; apply apresent_writable, HW; lia | apply Forall_nil].
Qed.

End w.
