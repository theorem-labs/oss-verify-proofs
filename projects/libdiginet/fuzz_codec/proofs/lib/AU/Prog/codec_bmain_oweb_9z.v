(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 636 of its 666 lines of code are new or changed and 219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_owebl.v, with its module names changed; 212 of its 254 lines of code are new or changed and 624 lines of the source are left out. *)
(* The end of segment OWE9 (SCRIBBLE) of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v
   seg_owe 9), from owe_sysex's return to CHK:
     0x82f74 lhu a0,24(s7); lui a1,0x70; or a0,a0,a1; sw a0,176(s7)   want_key = a | 0x70000
     0x82f84 sb s11,6(s2); sb s11,7(s2)                              pl marked unusable again (f8 f8)
     0x82f8c j 0x82dd0; 0x82dd0 ld s9,128(s1)                         to CHK 0x82dd4
   o9_after: from the cut facts owe_sysex leaves (lib/AU/Prog/codec_bmain_owebl.v mcom_sh with the payload's
   shadow map o9_shS and s9 any value, the record with owe_sysex's answer) to inv_chk. The executor starts from
   bm_entry_sh with k.a as a two-byte chunk (ra2), want_key's window (rkey) and pl's two shadow bytes (rsh), and
   ends through bm_exit_sh with the frame's shadow map shm 0 and lib/AU/Prog/codec_bmain_oweb_9l.v k_at_key. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgSatU CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkImgU CPgWalkKeptU CPgWalkCallU CPgWalkFrameU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_encl codec_bmain_owel codec_bmain_owebl.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_oweb_10l codec_bmain_oweb_11 codec_bmain_oweb_9l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition o9_ra2 : YP09.region := bm_frame_region 216 218 216 216 [YP09.mkChunk 216 (CVal 2 (SOff 37 0))].
Definition o9_rkey : YP09.region := bm_frame_region 368 372 368 372 [].
Definition o9_rs2 : smem := [o9_ra2; o9_rkey; o9_rsh].
(* the bytes the end writes: the cursor's window (not changed), want_key, pl's two shadow bytes *)
Definition o9_zpost (g : ectx) (pos sp1 a : Z) : Prop :=
(sp1 + 184 <= a < sp1 + 200) \/ (FA g pos + 368 <= a < FA g pos + 372) \/
(shadow_addr (FA g pos) + 6 <= a < shadow_addr (FA g pos) + 8).

Ltac o9_unf := repeat (first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]).
Ltac o9_unf_in H := repeat (first [rewrite ew_ewset_other in H by lia | rewrite ew_havoc_old in H by lia]).
(* the write windows: the machine stack (atom 2), the frame (atom 33), the frame's shadow (atom 34) *)
Ltac o9_awr :=
  idtac;
  let U2 := lazymatch goal with H : bv_unsigned (ew _ 2) = _ |- _ => H end in
  let sp1 := lazymatch type of U2 with _ = ?s => s end in
  let U33 := lazymatch goal with H : bv_unsigned (ew _ 33) = FA _ _ |- _ => H end in
  let pos := lazymatch type of U33 with _ = FA _ ?p => p end in
  let U34 := lazymatch goal with H : bv_unsigned (ew _ 34) = shadow_addr (FA _ _) |- _ => H end in
  let EFA := lazymatch goal with H : frame_addr _ 3 _ = FA _ _ |- _ => H end in
  let spz := lazymatch goal with |- _ _ _ _ ?s _ _ _ _ _ => s end in
  lazymatch goal with |- ?aw ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (aw Ev rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ spz _ _ _ _ _ 2%nat (sp1 - spz));
    [reflexivity | o9_unf; rewrite U2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 3 pos 33%nat);
    [reflexivity | o9_unf; rewrite EFA; exact U33 | left; reflexivity | cbn [YP09.r_wlo]; lia
    | cbn [YP09.r_whi]; change (fs_frame_bytes 3) with 512; lia |]
  | eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 3 pos 34%nat);
    [reflexivity | o9_unf; rewrite EFA; exact U34 | left; reflexivity | cbn [YP09.r_wlo]; lia
    | cbn [YP09.r_whi]; change (fs_frame_bytes 3 / 8) with 64; lia |] ].
(* the windows lie in the kept fact's zone *)
Ltac o9_kwr zone :=
  idtac;
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; o9_unf_in Hb;
      repeat match goal with U : bv_unsigned (ew _ ?n) = _, Hb' : context [bv_unsigned (ew _ ?n)] |- _ =>
        rewrite U in Hb' end;
      unfold zone; lia | ]);
  destruct Hr.
Ltac o9_region HS i Hr :=
  lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
    let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (Hr : region_ok tfibsegs E (ms_mem ms) r) by (apply (st_ok_region_nth E ss ms i r HS); vm_compute; reflexivity)
  end.
Ltac o9_in := repeat (first [left; reflexivity | right]).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Local Notation rd W mem := (mrestrict (w_H W) mem).

Lemma o9_after : forall g pos sp1 ops c k od s9v ly3 S3 W3 regs3 mem3 md3 w dp,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 0 ->
frames S3 = [(3, pos)] -> mo_le MT (e_S g) S3 0 ->
mcom_sh B MT K XM_LIB g pos sp1 o9_shS s9v ly3 S3 W3 regs3 mem3 md3 -> ops_at ops regs3 -> cur_at g sp1 c W3 mem3 ->
k_at g pos (set_wantZ k (w ++ skipn (length w) (kz_want k)) (Z.of_nat (length w)) dp) W3 mem3 ->
rec_okZ k od -> kz_rc k = fst (enc_kZ k od) -> kz_want_rc k = 0 -> 0 <= kz_a k <= 127 ->
owe_kZ k od = (0, (w, KEY 7 (kz_a k), dp)) -> Forall (fun x => 0 <= x < 256) w ->
SRr tfibsegs W3 (cfg_at tfibsegs 0x82f74 regs3 mem3 md3) (inv_chk B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops c k od s9v ly3 S3 W3 regs3 mem3 md3 w dp HJ Hfr Hmo HC Hops Hcur Hkat Hrec Hrc Hwrc Ha Hspec Fw.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (bm_facts_sh B MT K XM_LIB LAWS g pos sp1 o9_shS s9v ly3 S3 W3 regs3 mem3 md3 0 HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & _).
change (fs_frame_bytes 3) with 512 in Hfceil. unfold BM_HI in Hchi.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 mem3 md3 3 pos HAR Hin) as (_ & _ & Happ).
rewrite EFA in Happ. change (fs_frame_bytes 3) with 512 in Happ.
pose proof HC as (_ & _ & R2 & _).
pose proof Hcur as (Hc & _ & _).
pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof HC as HPerm. do 49 (destruct HPerm as (_ & HPerm)).
assert (D8 : 0 <= FA g pos / 8 /\ 8 * (FA g pos / 8) <= FA g pos) by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
assert (D44 : FA g pos / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (Hfsh : FA g pos + 512 <= shadow_addr (FA g pos) \/ shadow_addr (FA g pos) + 64 <= FA g pos).
{ unfold in_app in Happ. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  destruct Happ as (_ & [Hlow | (Hh1 & Hh2)]); [left; lia|].
  right. assert (D4 : 2199291686912 <= FA g pos / 8) by (apply Z.div_le_lower_bound; lia). lia. }
pose proof Hkat as (HK & Hwf).
pose proof HK as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbefore & Gout & Vwrc & Gwant &
  Vwl & Vwk & Vwd).
cbn [kz_a set_wantZ] in Va.
set (ys := [kz_a k]).
set (E := bm_env g pos c regs3 ys).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (unfold E; rewrite (bm_ew_reg g pos c regs3 ys 2 2%bv eq_refl), R2; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; apply unsigned_lit_small; lia).
assert (E33 : ew E 33 = Z_to_bv 64 (FA g pos)) by (unfold E; apply bm_ew_F).
assert (U33 : bv_unsigned (ew E 33) = FA g pos) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by (unfold E; apply bm_ew_SH).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr (FA g pos))
  by (rewrite E34; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; apply bm_ew_SB).
assert (E37 : ew E 37 = Z_to_bv 64 (kz_a k)) by (unfold E; exact (bm_ew_y g pos c regs3 ys 0)).
(* the start state *)
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W3) mem3)) o9_rs2).
{ unfold o9_rs2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - unfold o9_ra2. apply (o9_frame_region_ok B LAWS E W3 mem3 md3 ly3 S3 pos 216 218 216 216 _ HAR Hin);
      [rewrite EFA; exact U33 | lia | lia | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E _ (frame_addr ly3 3 pos) 216 2 (SOff 37 0) (kz_a k)); [ | cbn; lia | cbn; lia |].
    + rewrite (bm_den_off E 37 (kz_a k) 0 E37) by lia. rewrite Z.add_0_r. reflexivity.
    + change (N.to_nat 2) with 2%nat. rewrite EFA. apply o9_vm42; [|lia].
      replace (FA g pos + 216) with (FA g pos + 192 + 24) by lia. exact Va.
  - unfold o9_rkey. apply (o10_fwin_ok B LAWS E W3 mem3 ly3 S3 md3 pos 368 372 368 372 HAR Hin);
      [rewrite EFA; exact U33 | lia | lia | lia | lia].
  - unfold o9_rsh. apply (o9_shwin_ok B LAWS E ly3 S3 W3 mem3 md3 pos 6 8 HAR Hin);
      [rewrite EFA; exact U34 | lia | lia | lia]. }
assert (Hpd : pairwise_disjoint E o9_rs2).
{ unfold o9_rs2, o9_ra2, o9_rkey, o9_rsh, bm_frame_region. cbn [pairwise_disjoint all_disjoint].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U33, U34. repeat split; lia. }
assert (Hap : Forall (fun r => all_disjoint E r bm_regs) o9_rs2).
{ pose proof (owe_img_frame_apart B LAWS ly3 S3 W3 mem3 md3 3 pos A_GOT_shadow 8 0 512 HAR Hin) as G1.
  pose proof (owe_img_frame_apart B LAWS ly3 S3 W3 mem3 md3 3 pos A_shadow_glob 8 0 512 HAR Hin) as G2.
  rewrite EFA in G1, G2. change (fs_frame_bytes 3) with 512 in G1, G2. unfold A_GOT_shadow, A_shadow_glob in G1, G2.
  specialize (G1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  specialize (G2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold o9_rs2, o9_ra2, o9_rkey, o9_rsh, bm_regs, bm_regs0, cw_regs, bm_spill_region, bm_cur_region, stack_region,
    got_region, bcell_region, bm_frame_region.
  repeat apply Forall_cons; try apply Forall_nil; cbn [app all_disjoint]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U33, ?U2, ?U34; unfold A_GOT_shadow, A_shadow_glob;
  unfold shadow_addr, SHADOW_OFF in *; repeat split; lia. }
pose proof (bm_entry_sh B MT K XM_LIB TL LAWS g pos sp1 o9_shS s9v ly3 S3 W3 regs3 mem3 md3 0 c 0x82f74 ys o9_rs2 []
  HJ Hfr HC Hcur ltac:(vm_compute; reflexivity) Hrs Hpd Hap I) as HS.
fold E in HS.
assert (HAE : env_agree 37 (bm_env g pos c regs3 ys) E) by apply env_agree_refl.
assert (SHOK : sh_ok tfibsegs CW_Bx [owe_SHk] E (mrestrict (w_H W3) mem3)).
{ apply Forall_cons; [|apply Forall_nil]. apply (o9_shk W3 mem3 E (FA g pos) Hf64 ltac:(lia) Happ); [|exact E33 | exact E32].
  intros j Hj. rewrite (HSH j ltac:(lia)). f_equal. apply o9_shS_k. lia. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ o9_zpost g pos sp1 a ->
  aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 0x82f74) with (Z_to_bv 64 0x82f74).
(* 0x82f74-0x82dd0: want_key, pl's shadow bytes, s9; to CHK *)
aj_run_to_sh tfibtbl_lib_ok HS HJ PC_CHK.
{ o9_awr. }
cw_keep ltac:(o9_kwr o9_zpost). repeat (rewrite wvb_collapse in * ).
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ => rename msv into msF end.
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
  assert (HAF : env_agree 37 (bm_env g pos c regs3 ys) Ev) by env_agree_chain HAE;
  assert (F33 : ew Ev 33 = Z_to_bv 64 (FA g pos)) by (o9_unf; exact E33);
  assert (F34 : ew Ev 34 = Z_to_bv 64 (shadow_addr (FA g pos))) by (o9_unf; exact E34);
  assert (F37 : ew Ev 37 = Z_to_bv 64 (kz_a k)) by (o9_unf; exact E37) end.
assert (UF33 : bv_unsigned (ew _ 33) = FA g pos) by (rewrite F33; apply unsigned_lit_small; lia).
assert (UF34 : bv_unsigned (ew _ 34) = shadow_addr (FA g pos))
  by (rewrite F34; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
(* the cursor, before the state is rewritten *)
assert (Hcur3 : cur_at g sp1 c W3 (ms_mem msF)).
{ apply (bm_cur_end g pos c regs3 ys _ _ W3 msF sp1 HAF HS ltac:(vm_compute; o9_in) R2); unfold BM_HI in *; lia. }
(* want_key and the two shadow bytes the run wrote *)
o9_region HS 6%nat Hr6. o9_region HS 7%nat Hr7.
change (ms_mem (restrict (w_H W3) msF)) with (mrestrict (w_H W3) (ms_mem msF)) in Hr6, Hr7.
pose proof (o9_chunk_aview _ W3 _ _ (shadow_addr (FA g pos)) 6 _ Hr7
  ltac:(cbn [YP09.r_base base_val]; exact UF34) ltac:(o9_in)) as SF6.
pose proof (o9_chunk_aview _ W3 _ _ (shadow_addr (FA g pos)) 7 _ Hr7
  ltac:(cbn [YP09.r_base base_val]; exact UF34) ltac:(o9_in)) as SF7.
cbn [sv_denot] in SF6, SF7. rewrite unsigned_lit_small in SF6, SF7 by lia.
change (18446744073709551608 mod 256) with 248 in SF6, SF7.
unfold bm_frame_region in Hr6.
pose proof (field_of_region_any _ _ 33 (FA g pos) _ 368 372 368 372 368 4 _ Hr6 UF33 ltac:(o9_in) ltac:(lia)) as VK.
change (N.to_nat 4) with 4%nat in VK.
lazymatch type of VK with val_mem _ _ _ _ (bv_unsigned (sv_denot ?Ev ?e) mod _) =>
  assert (UK : U Ev e = KEY 7 (kz_a k))
    by (apply (o11_U_byte Ev 37 e (kz_a k) (fun y => KEY 7 y) F37);
        [lia | vm_compute; reflexivity | intros; vm_compute; reflexivity]) end.
unfold U in UK. rewrite UK in VK.
assert (VK' : val_mem tfibsegs (rd W3 (ms_mem msF)) (FA g pos + 192 + 176) 4 (KEY 7 (kz_a k))).
{ replace (FA g pos + 192 + 176) with (FA g pos + 368) by lia. apply (o11_vm _ _ 4 _ _ VK).
  change (8 * Z.of_nat 4) with 32. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). apply Z.mod_mod. lia. }
pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Ems.
lazymatch goal with HS : st_ok _ ?Ev ?ssv _ |- _ =>
  assert (R25 : getr (ms_regs msF) 25 = w64 (FA g pos + 448))
    by (rewrite (st_ok_restrict_reg tfibsegs (w_H W3) Ev ssv msF 25%bv HS);
        change (sr_get (ss_regs ssv) 25%bv) with (SOff 33 448);
        apply (bm_den_off Ev 33 (FA g pos) 448 F33); lia);
  assert (R20 : getr (ms_regs msF) 20 = getr regs3 20)
    by (rewrite (st_ok_restrict_reg tfibsegs (w_H W3) Ev ssv msF 20%bv HS);
        change (sr_get (ss_regs ssv) 20%bv) with (SOff 20 0);
        cbn [sv_denot]; destruct HAF as (HA & _); rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 20%nat ltac:(lia));
        apply (bm_ew_reg g pos c regs3 ys 20 20%bv eq_refl)) end.
rewrite Ems in HS. rewrite Ems.
change (Z_to_bv 64 (ss_pc _)) with (Z_to_bv 64 PC_CHK).
apply SRr_ret.
eexists ly3, S3, (ms_regs msF), (ms_mem msF), _, 0.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfr|]. split; [unfold EV_LIB; lia|]. split; [exact Hmo|].
split.
{ apply (mcommon_of_sh B MT K XM_LIB g pos sp1 0 ly3 S3 W3 (ms_regs msF) (ms_mem msF) _).
  lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ (mkst _ ?pcv _ _)) =>
  apply (bm_exit_sh B MT K XM_LIB LAWS g pos sp1 o9_shS s9v (shm 0) (FA g pos + 448) c ys ly3 S3 W3 regs3 mem3 md3
    ly3 S3 W3 (ms_regs msF) (ms_mem msF) _ 0 pcv ssv Ev HC HJ) end.
  - destruct HAF as (HA & HD). split; [intros n Hn; apply HA; lia | exact HD].
  - exact HS.
  - vm_compute. reflexivity.
  - exact R25.
  - intros a Ha'. unfold bm_keepzone in Ha'. apply KE; [unfold BM_HI in *; lia|].
    unfold o9_zpost. intros Hz. unfold shadow_addr, SHADOW_OFF, BM_HI in *. lia.
  - intros i Hi.
    destruct (Z.eq_dec i 6) as [-> | H6]; [rewrite SF6; reflexivity|].
    destruct (Z.eq_dec i 7) as [-> | H7]; [rewrite SF7; reflexivity|].
    rewrite KE; [| unfold shadow_addr, SHADOW_OFF in *; lia | unfold o9_zpost, shadow_addr, SHADOW_OFF in *; lia].
    rewrite (HSH i Hi). f_equal. apply o9_shS_other; lia.
  - exact HPerm. }
split.
{ destruct Hops as (Ho1 & Ho2). split; [exact Ho1|]. rewrite R20. exact Ho2. }
exists c, (owe_setZ (set_wantZ k (w ++ skipn (length w) (kz_want k)) (Z.of_nat (length w)) dp)
  (kz_want_rc k) (w ++ skipn (length w) (kz_want k)) (Z.of_nat (length w)) (KEY 7 (kz_a k)) dp), od.
split; [exact Hcur3|].
split.
{ apply (k_at_key g pos _ (KEY 7 (kz_a k)) W3 W3 mem3 (ms_mem msF) Hkat (o9_key_rng _ Ha)).
  - intros x Hx Hx2. apply KE; [lia|]. unfold o9_zpost. lia.
  - exact VK'. }
split; [exact Hrec|]. split; [exact Hrc|].
replace (owe_setZ (set_wantZ k (w ++ skipn (length w) (kz_want k)) (Z.of_nat (length w)) dp)
  (kz_want_rc k) (w ++ skipn (length w) (kz_want k)) (Z.of_nat (length w)) (KEY 7 (kz_a k)) dp)
  with (owe_setZ k 0 (w ++ skipn (length w) (kz_want k)) (Z.of_nat (length w)) (KEY 7 (kz_a k)) dp)
  by (unfold owe_setZ, set_wantZ; rewrite Hwrc; reflexivity).
apply (owe_want_ok_succ k od _ w (KEY 7 (kz_a k)) dp Hspec).
rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
symmetry. apply o11_u8_id. exact Fw.
Qed.
End b.
End a.
