(* RUN 0x820d0-0x820f0 of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v seg_run): run()'s
   switch on the kind.
     0x820d0 lw a0,0(s6)        a0 = k.kind (s6 = k = F + 176)
     0x820d4 bltu s11,a0,0x821f4  10 < kind: ENC11 (SYSEX)
     0x820d8 .. 0x820f0          a0 = kind * 4 + 0x20ee4, lw a0,0(a0), a0 += 0x20ee4, jr a0: run()'s table, ENCk
   No store and no instrumented check: the walk reads k.kind and one word of the image's table at 0x20ee4.
   The proof splits on the kind (0 .. 11, enc_okZ) and runs the executor once per kind, from a state holding the
   kind as a literal chunk of k (atom 33 = F, offset 176) and the table's 44 bytes as the image's own (CPgWalkImg's
   cpg_img_region), to enc_pc kind; the end state is the cut inv_enc by the exit bridge am_exit / am_mcut of
   lib/A/Prog/codec_amain_st.v. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnSpec DgnLib.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk CPgWalkImg.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem codec_amain_encl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition RUN_TBL : Z := 0x20ee4.
(* k.kind as a literal *)
Definition run_rk (kd : Z) : YP09.region := am_frame_region 176 180 176 176 [YP09.mkChunk 176 (CVal 4 (SLit kd))].
(* run()'s table: 11 words *)
Definition run_rt : YP09.region := cpg_img_region RUN_TBL 44.
(* the base without the .got slot and the cell (s4 already holds the shadow offset; the walk makes no check) *)
Definition run_base : smem := [stack_region 0; am_spill_region; am_cur_region].
Definition run_ss (kd : Z) : sstate :=
mkSS PC_RUN am_sregs (run_rk kd :: run_rt :: run_base) None (mkFacts am_atoms [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the table's bytes are bytes of the image *)
Lemma run_tbl_img : forall a, RUN_TBL <= a < RUN_TBL + 44 -> in_img tfibsegs a.
Proof.
intros a Ha. destruct (am_in_ro RUN_TBL 44 ltac:(vm_compute; reflexivity) a Ha) as [(s & Hs & _ & Hr) | Hr].
- exists s. split; [exact Hs | exact Hr].
- unfold CA_RLO, RUN_TBL in *. lia.
Qed.

Lemma run_start : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c kd,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176) 4 kd -> 0 <= kd <= 11 ->
st_ok tfibsegs (am_env g pos c regs2 []) (run_ss kd)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_RUN) mem2 (seg_rom tfibsegs))).
Proof.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c kd HJ Hfr HC Hcur Vk Hkd.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
unfold AM_HI in Hchi.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HC as (Hpre & _ & R2 & _).
set (E := am_env g pos c regs2 []).
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c PC_RUN [] [] []
  HJ Hfr HC Hcur eq_refl (Forall_nil _) I (Forall_nil _) I) as HS0.
fold E in HS0.
pose proof (st_ok_submem tfibsegs E (am_ss PC_RUN [] []) _ run_base HS0
  ltac:(cbn [am_ss am_ssb ss_mem]; unfold am_regs, am_regs0, cw_regs, run_base; cbn [app]; submem_to)
  ltac:(vm_compute; reflexivity)) as HS1.
cbn [am_ss am_ssb ss_pc ss_regs ss_resv ss_facts] in HS1. rewrite app_nil_r in HS1.
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 [] 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (am_ew_F g pos c regs2 []). apply unsigned_lit_small. lia. }
(* the table *)
pose proof (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly2 S2 W2 mem2 md2 kev Hpre HJ) as HRO.
assert (Hrt : region_ok tfibsegs E (mrestrict (w_H W2) mem2) run_rt).
{ apply (cpg_img_region_ok B CA_RLO CA_RHI E W2 mem2 RUN_TBL 44).
  - exact HRO.
  - exact (am_in_ro RUN_TBL 44 ltac:(vm_compute; reflexivity)).
  - intros a Ha. apply (proj1 (tl_lib_consts B TL a ltac:(unfold lib_const_addr, RUN_TBL in *; lia))).
  - intros a Ha. apply (proj2 (tl_lib_consts B TL a ltac:(unfold lib_const_addr, RUN_TBL in *; lia))).
  - vm_compute. reflexivity.
  - unfold RUN_TBL. lia.
  - lia.
  - unfold RUN_TBL. lia. }
pose proof (ast_ok_add_region tfibsegs E _ _ run_rt HS1 eq_refl Hrt) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
specialize (HS2 ltac:(unfold run_base, run_rt, cpg_img_region, stack_region, am_spill_region, am_cur_region;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U2;
  unfold RUN_TBL; repeat split; lia)).
(* k.kind *)
assert (Hrk : region_ok tfibsegs E (mrestrict (w_H W2) mem2) (run_rk kd)).
{ apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c [] 176 180 176 176
    _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E _ (FA g pos) 176 4 (SLit kd) kd); [reflexivity | cbn; lia | cbn; lia | exact Vk]. }
pose proof (ast_ok_add_region tfibsegs E _ _ (run_rk kd) HS2 eq_refl Hrk) as HS3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
apply HS3.
unfold run_base, run_rt, run_rk, cpg_img_region, am_frame_region, stack_region, am_spill_region, am_cur_region.
cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U33.
split; [|repeat split; lia].
(* the record is in the frame, the table in the image *)
destruct (Z_le_gt_dec (FA g pos + 180) RUN_TBL) as [Hle | Hgt]; [left; exact Hle|].
destruct (Z_le_gt_dec (RUN_TBL + 44) (FA g pos + 176)) as [Hle2 | Hgt2]; [right; exact Hle2|].
exfalso.
apply (frm_img tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos (Z.max (FA g pos + 176) RUN_TBL) HAR Hin);
  [rewrite EFA; change (fs_frame_bytes 3) with 512; lia|].
apply run_tbl_img. lia.
Qed.

(* ENCk: the executor state of the run, at enc_pc kind, with nothing written outside the cursor window *)
Lemma run_exit : forall g pos sp1 ops kind c k od ly2 S2 W2 regs2 mem2 md2 kev E ss ms md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 -> cur_at g sp1 c W2 mem2 ->
k_at g pos k W2 mem2 -> enc_okZ k od -> kz_kind k = kind -> 0 <= kind <= 11 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 kev ->
env_agree 37 (am_env g pos c regs2 []) E ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_pc ss = enc_pc kind -> ss_resv ss = None ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
nth_error (ss_mem ss) 4 = Some am_cur_region ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 152 <= a < sp1 + 168) ->
 aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
SRr tfibsegs W2 {| cfg_ms := ms; cfg_model := md3 |}
  (fun W3 c3 => exists kind, inv_enc B MT K XM_LIB g pos sp1 ops kind W3 c3).
Proof.
intros g pos sp1 ops kind c k od ly2 S2 W2 regs2 mem2 md2 kev E ss ms md3
  HJ Hfr Hk Hmo HC Hops Hcur Hkat Henc Ekind Hkd HJ3 HAG HS Hpc Hresv Hkeep H26 Hcr KE.
apply SRr_ret. exists kind.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E ss ms HS Hresv) as Ems.
rewrite Hpc in Ems.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof HC as (Hpre & _ & R2 & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof Hcur as (Hc & _ & _).
pose proof HS as HS'. rewrite Ems in HS'.
assert (HAG35 : env_agree 35 (am_env g pos c regs2 []) E).
{ destruct HAG as (HA & HD). split; [intros n Hn'; apply HA; lia | exact HD]. }
assert (HC3 : mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3).
{ apply (am_exit B MT K XM_LIB LAWS g pos sp1 0 0 c [] ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3
    kev (Z_to_bv 64 (enc_pc kind)) ss E HC HJ3 HAG35 HS' Hkeep).
  - intros a Ha. unfold am_keepzone in Ha. apply KE; [lia | lia].
  - intros i Hi. pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
    rewrite <- (HSH' i Hi). apply KE.
    + unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. unfold AM_HI in *. lia.
    + unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. unfold AM_HI in *. lia.
  - pose proof HC as HPerm. do 45 (destruct HPerm as (_ & HPerm)). exact HPerm. }
rewrite Ems.
change {| cfg_ms := mkst (ms_regs ms) (Z_to_bv 64 (enc_pc kind)) (ms_mem ms) (seg_rom tfibsegs); cfg_model := md3 |}
  with (cfg_at tfibsegs (enc_pc kind) (ms_regs ms) (ms_mem ms) md3).
unfold inv_enc.
apply (am_mcut B MT K XM_LIB g pos sp1 0 (enc_pc kind) _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 kev HJ3 Hfr Hk Hmo HC3).
cbv beta. split; [|split; [exact Hkd|]].
- destruct Hops as (Hops & R26). split; [exact Hops|].
  rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E ss ms 26%bv HS), H26.
  destruct HAG as (HA & _). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 26%nat ltac:(lia)).
  rewrite (am_ew_reg g pos c regs2 [] 26 26%bv eq_refl). exact R26.
- exists c, k, od. split.
  + apply (am_cur_end g pos c regs2 [] E ss W2 ms sp1 HAG HS (nth_error_In _ _ Hcr) R2); unfold AM_HI in *; lia.
  + split; [|split; [exact Henc | exact Ekind]].
    apply (k_at_kept g pos k W2 W2 mem2 (ms_mem ms) Hkat). intros x Hx. apply KE; unfold AM_HI in *; lia.
Qed.

(* one kind: the run to ENCk and the exit *)
Ltac run_case HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Henc HAE :=
  lazymatch goal with Ek : kz_kind ?k = ?kd, HS : st_ok _ _ (run_ss (kz_kind ?k)) _ |- _ =>
    rewrite Ek in HS;
    let p := eval vm_compute in (enc_pc kd) in
    cw_run_to cw_awr_stk p; cw_keep cw_kwr_stk;
    lazymatch goal with HS2 : st_ok _ _ _ (restrict _ ?msv), HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msv) _ _ |- _ =>
      eapply (run_exit _ _ _ _ kd _ k _ _ _ _ _ _ _ _ _ _ msv _ HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Henc Ek ltac:(lia) HJ2 HAE HS2);
      [vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity
      | lazymatch goal with KE2 : forall a, _ -> ~ _ -> aview _ _ (ms_mem msv) a = _ |- _ => exact KE2 end]
    end
  end.

Theorem seg_run_holds : seg_run B MT K XM_LIB.
Proof.
intros g pos sp1 ops W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC &
  (Hops & c & k & od & Hcur & Hkat & Henc)).
pose proof Henc as (Hkind & _).
pose proof Hkat as ((Vk & _) & _).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof HC as (Hpre & _ & R2 & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
unfold cfg_at. change (w64 PC_RUN) with (Z_to_bv 64 PC_RUN).
pose proof (run_start g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c (kz_kind k) HJ Hfr HC Hcur Vk Hkind) as HS.
remember (am_env g pos c regs2 []) as E eqn:HEE.
assert (HAE : env_agree 37 (am_env g pos c regs2 []) E) by (subst E; apply env_agree_refl).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 [] 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. unfold AM_HI in *. lia. }
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 152 <= a < sp1 + 168) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
cw_keep_j0 HJ HJ0.
assert (Ek : kz_kind k = 0 \/ kz_kind k = 1 \/ kz_kind k = 2 \/ kz_kind k = 3 \/ kz_kind k = 4 \/ kz_kind k = 5 \/
  kz_kind k = 6 \/ kz_kind k = 7 \/ kz_kind k = 8 \/ kz_kind k = 9 \/ kz_kind k = 10 \/ kz_kind k = 11) by lia.
repeat (destruct Ek as [Ek | Ek]; [run_case HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Henc HAE|]).
run_case HJ0 Hfr Hk Hmo HC Hops Hcur Hkat Henc HAE.
Qed.
End b.
End a.
