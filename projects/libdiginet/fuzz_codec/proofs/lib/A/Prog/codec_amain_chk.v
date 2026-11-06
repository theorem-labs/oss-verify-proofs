(* Segment CHK of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v seg_chk), 0x8273c-0x82758,
   to LATCH 0x8275c:
     0x8273c mv a0,s6; jal check_refusal (0x844dc, returns to 0x82744)
     0x82744 mv a0,s6; jal check_range (0x84590, returns to 0x8274c)
     0x8274c lw a0,72(s6) (k.rc); bnez a0 -> 0x8275c
     0x82754 mv a0,s6; jal check_bytes (0x84640, returns to 0x8275c)
   No instrumented check (k.rc is at a constant offset of the frame). Between the calls the cut is chk_at: the record
   k and the cursor fixed, k marked usable. Each run of the engine (the argument move and the `jal`, or the load and
   the branch) writes no byte, so its state holds no writable region (chk_start keeps only the segment's own
   read-only regions) and every byte is kept (chk_stop). Each call goes through the callee's A-level contract: its
   premises at the entry (codec_amain_encl.v's enc_entry: cdc_entry; chk_rd: k's 184 bytes readable and marked
   usable) and the cut facts back at the return from its post (chk_call, on codec_amain_encl.v's am_call_kept and
   k_at_kept; the three checks write nothing, cno_wr). The record premises of the three contracts are
   lib/A/Prog/codec_amain_lem.v's amain_chk_facts. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgChkC CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalk CPgWalkCall CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
codec_amain_inv codec_amain_lem codec_amain_st codec_amain_encl codec_amain_owel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the state at 0x8274c ================================ *)
(* k.rc (4 bytes at k + 72 = F + 248), read-only, as atom 37 (its value modulo 2 ^ 32) *)
Definition chk_rk : YP09.region := am_frame_region 248 252 248 248 [YP09.mkChunk 248 (CVal 4 (SOff 37 0))].

(* every region of the state is read-only *)
Ltac chk_awr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]].

(* a 32-bit field read back from its value modulo 2 ^ 32 *)
Lemma chk_rc0 : forall r, - 2 ^ 31 <= r < 2 ^ 31 -> (r mod 2 ^ 32 = 0 <-> r = 0).
Proof.
intros r Hr. pose proof (Z.div_mod r (2 ^ 32) ltac:(lia)) as D.
pose proof (Z.mod_pos_bound r (2 ^ 32) ltac:(lia)) as M. split; intros H; [lia|]. subst r. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ACR : cdc_check_refusal_specX tfibsegs B MT AM_check_refusal.
Hypothesis ACG : cdc_check_range_specX tfibsegs B MT AM_check_range.
Hypothesis ACB : cdc_check_bytes_specX tfibsegs B MT AM_check_bytes.

(* the cut inside CHK: at pc, the pass counter, the cursor at c and the record k; k marked usable *)
Definition chk_at (g : ectx) (pos sp1 ops c : Z) (k : kcallZ) (pc : Z) : world tfibsegs -> config -> Prop :=
mcut B MT K XM_LIB g pos sp1 0 pc (fun _ _ W2 regs2 mem2 _ =>
  ops_at ops regs2 /\ cur_at g sp1 c W2 mem2 /\ k_at g pos k W2 mem2).

(* ================================ the executor states ================================ *)
(* the state at pc with only the regions rs (each read-only), from a cut's parts *)
Lemma chk_start : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c ys pc (rs : smem),
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
regions_wf rs = true ->
Forall (region_ok tfibsegs (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2)) rs ->
pairwise_disjoint (am_env g pos c regs2 ys) rs ->
Forall (fun r => all_disjoint (am_env g pos c regs2 ys) r am_regs) rs ->
st_ok tfibsegs (am_env g pos c regs2 ys) (mkSS pc am_sregs rs None (mkFacts (am_atoms ++ []) [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs))).
Proof.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c ys pc rs HJ Hfr HC Hcur Hwf Hrs Hpd Hap.
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c pc ys rs []
  HJ Hfr HC Hcur Hwf Hrs Hpd Hap I) as HS0.
apply (st_ok_submem tfibsegs _ (am_ss pc rs []) _ rs HS0); [|exact Hwf].
cbn [am_ss am_ssb ss_mem]. unfold am_regs, am_regs0, cw_regs. cbn [app].
do 5 apply submem_drop. apply submem_refl.
Qed.

(* the cut's parts at the stop of a run that wrote no byte *)
Lemma chk_stop : forall g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 -> cur_at g sp1 c W2 mem2 ->
k_at g pos k W2 mem2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 kev ->
env_agree 37 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_resv ss = None ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 /\ ops_at ops (ms_regs ms) /\
cur_at g sp1 c W2 (ms_mem ms) /\ k_at g pos k W2 (ms_mem ms).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3
  HJ Hfr HC Hops Hcur Hkat HJ3 HAG HS Hresv Hkeep H26 KE.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E ss ms HS Hresv) as Ems.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
unfold AM_HI in *.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a)
  by (intros a Ha; exact (KE a Ha (fun H => H))).
pose proof HS as HS'. rewrite Ems in HS'.
assert (HAG35 : env_agree 35 (am_env g pos c regs2 ys) E).
{ destruct HAG as (HA & HD). split; [intros n Hn'; apply HA; lia | exact HD]. }
pose proof Hcur as (Hc & C152 & C160).
split; [|split; [|split]].
- apply (am_exit B MT K XM_LIB LAWS g pos sp1 0 0 c ys ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3
    kev (Z_to_bv 64 (ss_pc ss)) ss E HC HJ3 HAG35 HS' Hkeep).
  + intros a Ha. unfold am_keepzone in Ha. apply KA. lia.
  + intros i Hi. pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
    rewrite <- (HSH' i Hi). apply KA.
    unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. lia.
  + pose proof HC as HPerm. do 45 (destruct HPerm as (_ & HPerm)). exact HPerm.
- destruct Hops as (Hops & R26). split; [exact Hops|].
  rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E ss ms 26%bv HS), H26.
  destruct HAG as (HA & _). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 26%nat ltac:(lia)).
  rewrite (am_ew_reg g pos c regs2 ys 26 26%bv eq_refl). exact R26.
- split; [exact Hc|]. split.
  + apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact C152].
    intros x Hx. apply KA. cbn in Hx. lia.
  + apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact C160].
    intros x Hx. apply KA. cbn in Hx. lia.
- apply (k_at_kept g pos k W2 W2 mem2 (ms_mem ms) Hkat). intros x Hx. apply KA. lia.
Qed.

(* the cut chk_at at the stop of such a run *)
Lemma chk_stop_at : forall g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 -> cur_at g sp1 c W2 mem2 ->
k_at g pos k W2 mem2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 kev ->
env_agree 37 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_resv ss = None ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
chk_at g pos sp1 ops c k (ss_pc ss) W2 (mkCfg ms md3).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3
  HJ Hfr Hk Hmo HC Hops Hcur Hkat HJ3 HAG HS Hresv Hkeep H26 KE.
destruct (chk_stop g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys E ss ms md3
  HJ Hfr HC Hops Hcur Hkat HJ3 HAG HS Hresv Hkeep H26 KE) as (HC3 & Hops3 & Hcur3 & Hkat3).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W2) E ss ms HS Hresv).
exists ly2, S2, (ms_regs ms), (ms_mem ms), md3, kev. split; [reflexivity|].
split; [exact HJ3|]. split; [exact Hfr|]. split; [exact Hk|]. split; [exact Hmo|]. split; [exact HC3|].
split; [exact Hops3|]. split; [exact Hcur3 | exact Hkat3].
Qed.

(* k's 184 bytes are readable and marked usable at a call state of the walk, off the callee's window *)
Lemma chk_rd : forall g pos sp1 ly2 S2 W2 regs mem md kev T,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
0 <= T -> 320 + T <= T_main_need ->
crd_ok tfibsegs W2 mem (spZ regs) T (FA g pos + 176) 184.
Proof.
intros g pos sp1 ly2 S2 W2 regs mem md kev T HJ Hfr HC HT HTn.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
pose proof HC as (_ & _ & R2 & _).
pose proof HJ as (HAR & _).
assert (FFS : LLVMF_STK = 32768) by reflexivity. unfold T_main_need in HTn.
assert (Usp : spZ regs = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold AM_HI in *; lia).
rewrite Usp.
apply (sat_main_k_rd tfibsegs B LAWS ly2 S2 W2 mem md sp1 T pos (FA g pos) LLVMF_STK (e_sp0 g) HAR
  ltac:(rewrite Hfr; left; reflexivity) EFA Hf64 (am_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 regs mem md HC)); lia.
Qed.

(* from a call state of the walk and the callee's post (writing nothing), the cut chk_at at the return address *)
Lemma chk_call : forall g pos sp1 ops c k ly2 S2 W2 regs mem md kev T a ra,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
ops_at ops regs -> cur_at g sp1 c W2 mem -> k_at g pos k W2 mem ->
getr regs 1 = w64 ra ->
SRr tfibsegs W2 (cfg_at tfibsegs a regs mem md)
  (cdc_post tfibsegs B MT LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] kev regs T
     cno_wr ly2 S2 W2 mem md (fun _ _ _ => True)) ->
SRr tfibsegs W2 (cfg_at tfibsegs a regs mem md) (chk_at g pos sp1 ops c k ra).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs mem md kev T a ra HJ Hfr Hk Hmo HC Hops Hcur Hkat R1 HP.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & _).
eapply SRr_mono; [exact HP|]. intros W3 c3 _ Hpost.
destruct Hpost as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HPR & Hfr3 & HPerm & _ & Hmo3 & HK & _).
unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
destruct (am_call_kept B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs mem md kev c T cno_wr
  ly3 S3 W3 regs3 mem3 md3 kev HJ Hfr HC Hcur ltac:(unfold cno_wr; intros x Hx; destruct Hx) HJ3 HPR HPerm HK)
  as (HC3 & Hcur3 & KF).
assert (HPR26 : getr regs3 26 = getr regs 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
exists ly3, S3, regs3, mem3, md3, kev. split; [rewrite R1; reflexivity|].
split; [exact HJ3|]. split; [rewrite Hfr3; exact Hfr|]. split; [exact Hk|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo Hmo3)|]. split; [exact HC3|].
split; [destruct Hops as [Ho1 Ho2]; split; [exact Ho1 | rewrite HPR26; exact Ho2]|].
split; [exact Hcur3|].
apply (k_at_kept g pos k W2 W3 mem mem3 Hkat). intros x Hx. apply KF; [lia | unfold cno_wr; intros []].
Qed.

(* the three calls, at a call state of the walk with a0 = &k and ra the return address *)
Lemma chk_ref_call : forall g pos sp1 ops c k ly2 S2 W2 regs mem md kev,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
ops_at ops regs -> cur_at g sp1 c W2 mem -> k_at g pos k W2 mem ->
getr regs 1 = Z_to_bv 64 0x82744 -> getr regs 10 = w64 (FA g pos + 176) ->
~ (kz_kind k = 11 /\ kz_b k = 0x70 /\ kz_rc k = 0) ->
SRr tfibsegs W2 (cfg_at tfibsegs AM_check_refusal regs mem md) (chk_at g pos sp1 ops c k 0x82744).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs mem md kev HJ Hfr Hk Hmo HC Hops Hcur Hkat R1 R10 Hn.
apply (chk_call g pos sp1 ops c k ly2 S2 W2 regs mem md kev T_check_refusal AM_check_refusal 0x82744
  HJ Hfr Hk Hmo HC Hops Hcur Hkat R1).
pose proof Hkat as (Hka & Hwf).
apply (ACR LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev regs
  (FA g pos + 176) k).
- apply (enc_entry B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs mem md kev T_check_refusal 0x82744 HJ Hfr Hk HC R1);
    first [lia | reflexivity | apply Z.leb_le; vm_compute; reflexivity].
- exact R10.
- exact Hka.
- exact Hwf.
- apply (chk_rd g pos sp1 ly2 S2 W2 regs mem md kev T_check_refusal HJ Hfr HC);
    apply Z.leb_le; vm_compute; reflexivity.
- exact Hn.
Qed.

Lemma chk_rng_call : forall g pos sp1 ops c k ly2 S2 W2 regs mem md kev,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
ops_at ops regs -> cur_at g sp1 c W2 mem -> k_at g pos k W2 mem ->
getr regs 1 = Z_to_bv 64 0x8274c -> getr regs 10 = w64 (FA g pos + 176) ->
(kz_rc k <> 0 -> kz_out k = kz_before k) -> kz_rc k = kz_want_rc k ->
SRr tfibsegs W2 (cfg_at tfibsegs AM_check_range regs mem md) (chk_at g pos sp1 ops c k 0x8274c).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs mem md kev HJ Hfr Hk Hmo HC Hops Hcur Hkat R1 R10 Ho Hw.
apply (chk_call g pos sp1 ops c k ly2 S2 W2 regs mem md kev T_check_range AM_check_range 0x8274c
  HJ Hfr Hk Hmo HC Hops Hcur Hkat R1).
pose proof Hkat as (Hka & Hwf).
apply (ACG LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev regs
  (FA g pos + 176) k).
- apply (enc_entry B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs mem md kev T_check_range 0x8274c HJ Hfr Hk HC R1);
    first [lia | reflexivity | apply Z.leb_le; vm_compute; reflexivity].
- exact R10.
- exact Hka.
- exact Hwf.
- apply (chk_rd g pos sp1 ly2 S2 W2 regs mem md kev T_check_range HJ Hfr HC);
    apply Z.leb_le; vm_compute; reflexivity.
- exact Ho.
- exact Hw.
Qed.

Lemma chk_byt_call : forall g pos sp1 ops c k ly2 S2 W2 regs mem md kev,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs mem md ->
ops_at ops regs -> cur_at g sp1 c W2 mem -> k_at g pos k W2 mem ->
getr regs 1 = Z_to_bv 64 0x8275c -> getr regs 10 = w64 (FA g pos + 176) ->
kz_want_len k = cmd_lenZ (kz_out k) -> kz_want_len k <= 24 ->
firstn (Z.to_nat (kz_want_len k)) (kz_out k) = firstn (Z.to_nat (kz_want_len k)) (kz_want k) ->
cmd_keyZ (kz_out k) = kz_want_key k -> cmd_displayZ (kz_out k) = kz_want_display k ->
SRr tfibsegs W2 (cfg_at tfibsegs AM_check_bytes regs mem md) (chk_at g pos sp1 ops c k PC_LATCH).
Proof.
intros g pos sp1 ops c k ly2 S2 W2 regs mem md kev HJ Hfr Hk Hmo HC Hops Hcur Hkat R1 R10 B1 B2 B3 B4 B5.
apply (chk_call g pos sp1 ops c k ly2 S2 W2 regs mem md kev T_check_bytes AM_check_bytes PC_LATCH
  HJ Hfr Hk Hmo HC Hops Hcur Hkat R1).
pose proof Hkat as (Hka & Hwf).
apply (ACB LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem md kev regs
  (FA g pos + 176) k).
- apply (enc_entry B MT K XM_LIB LAWS g pos sp1 ly2 S2 W2 regs mem md kev T_check_bytes 0x8275c HJ Hfr Hk HC R1);
    first [lia | reflexivity | apply Z.leb_le; vm_compute; reflexivity].
- exact R10.
- exact Hka.
- exact Hwf.
- apply (chk_rd g pos sp1 ly2 S2 W2 regs mem md kev T_check_bytes HJ Hfr HC);
    apply Z.leb_le; vm_compute; reflexivity.
- exact B1.
- exact B2.
- exact B3.
- exact B4.
- exact B5.
Qed.

(* ================================ the run to a callee's entry and the call ================================
   At the stop of a run at the callee's entry: the cut's parts there (chk_stop), a0 and ra read off the state, and the
   call through the lemma LEM (one of the three above, applied to its leading arguments). *)
Ltac chk_do_call g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys HJ0 Hfr Hk Hmo HC Hops Hcur Hkat UF LEM :=
  lazymatch goal with
  | HS : st_ok tfibsegs ?Ev ?ssv (restrict (w_H _) ?msv), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msv) ?mdv _,
    HAE : env_agree 37 _ ?Ev, KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- SRr _ _ (mkCfg ?msv ?mdv') ?Q =>
    let HCc := fresh "HCc" in let Hopsc := fresh "Hopsc" in let Hcurc := fresh "Hcurc" in let Hkatc := fresh "Hkatc" in
    destruct (chk_stop g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys Ev ssv msv mdv
      HJ0 Hfr HC Hops Hcur Hkat HJ HAE HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) KE)
      as (HCc & Hopsc & Hcurc & Hkatc);
    let R1 := fresh "R1" in let R10 := fresh "R10" in
    rreg HS (1%bv : bv 5) R1; rreg HS (10%bv : bv 5) R10;
    rewrite UF in R10;
    eapply (cpw_call _ Ev ssv msv mdv' Q Q); [exact HS | reflexivity | cbn [ss_pc] |
      let W3 := fresh "W" in let c3 := fresh "c" in let H3 := fresh "H" in
      intros W3 c3 H3; apply SRr_ret; exact H3];
    apply (LEM ly2 S2 W2 (ms_regs msv) (ms_mem msv) mdv kev HJ Hfr Hk Hmo HCc Hopsc Hcurc Hkatc R1 R10)
  end.

(* ================================ the three pieces ================================ *)
(* 0x8273c-0x82740: check_refusal, to 0x82744 *)
Lemma chk_ph1 : forall g pos sp1 ops c k W2 c2,
chk_at g pos sp1 ops c k PC_CHK W2 c2 -> ~ (kz_kind k = 11 /\ kz_b k = 0x70 /\ kz_rc k = 0) ->
SRr tfibsegs W2 c2 (chk_at g pos sp1 ops c k 0x82744).
Proof.
intros g pos sp1 ops c k W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC & Hops & Hcur & Hkat) Hn.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
unfold AM_HI in Hchi.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (_ & _ & R2 & _).
pose proof (chk_start g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c [] PC_CHK [] HJ Hfr HC Hcur eq_refl
  (Forall_nil _) I (Forall_nil _)) as HS.
remember (am_env g pos c regs2 []) as E eqn:HEE.
assert (HAE : env_agree 37 (am_env g pos c regs2 []) E) by (subst E; apply env_agree_refl).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (am_ew_F g pos c regs2 []). apply unsigned_lit_small. lia. }
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
unfold cfg_at. change (w64 PC_CHK) with (Z_to_bv 64 PC_CHK).
cw_keep_j0 HJ HJ0.
cw_run_to chk_awr 0x844dc. cw_keep cw_kwr_ro.
chk_do_call g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev (@nil Z) HJ0 Hfr Hk Hmo HC Hops Hcur Hkat UF
  (chk_ref_call g pos sp1 ops c k).
exact Hn.
Qed.

(* 0x82744-0x82748: check_range, to 0x8274c *)
Lemma chk_ph2 : forall g pos sp1 ops c k W2 c2,
chk_at g pos sp1 ops c k 0x82744 W2 c2 ->
(kz_rc k <> 0 -> kz_out k = kz_before k) -> kz_rc k = kz_want_rc k ->
SRr tfibsegs W2 c2 (chk_at g pos sp1 ops c k 0x8274c).
Proof.
intros g pos sp1 ops c k W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC & Hops & Hcur & Hkat)
  Ho Hw.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
unfold AM_HI in Hchi.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (_ & _ & R2 & _).
pose proof (chk_start g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c [] 0x82744 [] HJ Hfr HC Hcur eq_refl
  (Forall_nil _) I (Forall_nil _)) as HS.
remember (am_env g pos c regs2 []) as E eqn:HEE.
assert (HAE : env_agree 37 (am_env g pos c regs2 []) E) by (subst E; apply env_agree_refl).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (am_ew_F g pos c regs2 []). apply unsigned_lit_small. lia. }
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
unfold cfg_at. change (w64 0x82744) with (Z_to_bv 64 0x82744).
cw_keep_j0 HJ HJ0.
cw_run_to chk_awr 0x84590. cw_keep cw_kwr_ro.
chk_do_call g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev (@nil Z) HJ0 Hfr Hk Hmo HC Hops Hcur Hkat UF
  (chk_rng_call g pos sp1 ops c k).
- exact Ho.
- exact Hw.
Qed.

(* 0x8274c-0x82758: k.rc, the branch, and check_bytes when k.rc = 0, to LATCH 0x8275c *)
Lemma chk_ph3 : forall g pos sp1 ops c k W2 c2,
chk_at g pos sp1 ops c k 0x8274c W2 c2 ->
(kz_rc k = 0 -> kz_want_len k = cmd_lenZ (kz_out k) /\ kz_want_len k <= 24 /\
   firstn (Z.to_nat (kz_want_len k)) (kz_out k) = firstn (Z.to_nat (kz_want_len k)) (kz_want k) /\
   cmd_keyZ (kz_out k) = kz_want_key k /\ cmd_displayZ (kz_out k) = kz_want_display k) ->
SRr tfibsegs W2 c2 (chk_at g pos sp1 ops c k PC_LATCH).
Proof.
intros g pos sp1 ops c k W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC & Hops & Hcur & Hkat)
  Hby.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
unfold AM_HI in Hchi.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HC as (_ & _ & R2 & _).
pose proof Hkat as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & V72 & _) & Hwf).
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & Wrc & _).
set (ys := [kz_rc k mod 2 ^ 32]).
pose proof (Z.mod_pos_bound (kz_rc k) (2 ^ 32) ltac:(lia)) as Mrc.
assert (X37 : ew (am_env g pos c regs2 ys) 37 = Z_to_bv 64 (kz_rc k mod 2 ^ 32))
  by exact (am_ew_y g pos c regs2 ys 0).
assert (Hrk : region_ok tfibsegs (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) chk_rk).
{ apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c ys 248 252 248 248
    _ HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs _ _ (FA g pos) 248 4 (SOff 37 0) (kz_rc k mod 2 ^ 32));
    [ rewrite (am_den_off _ 37 (kz_rc k mod 2 ^ 32) 0 X37) by lia; rewrite Z.add_0_r; reflexivity
    | cbn; lia | cbn; lia |].
  replace (FA g pos + 248) with (FA g pos + 176 + 72) by lia. exact (cw_val_mem_mod _ _ 4 _ V72). }
assert (Hap : all_disjoint (am_env g pos c regs2 ys) chk_rk am_regs)
  by exact (owe_frame_apart_base B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c ys
     248 252 248 248 _ HJ Hfr HC ltac:(lia) ltac:(lia)).
pose proof (chk_start g pos sp1 ly2 S2 W2 regs2 mem2 md2 kev c ys 0x8274c [chk_rk] HJ Hfr HC Hcur
  ltac:(vm_compute; reflexivity) ltac:(apply Forall_cons; [exact Hrk | apply Forall_nil])
  ltac:(cbn [pairwise_disjoint all_disjoint]; repeat split)
  ltac:(apply Forall_cons; [exact Hap | apply Forall_nil])) as HS.
remember (am_env g pos c regs2 ys) as E eqn:HEE.
assert (HAE : env_agree 37 (am_env g pos c regs2 ys) E) by (subst E; apply env_agree_refl).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (am_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
assert (E37 : ew E 37 = Z_to_bv 64 (kz_rc k mod 2 ^ 32)) by (subst E; exact X37).
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
unfold cfg_at. change (w64 0x8274c) with (Z_to_bv 64 0x8274c).
cw_keep_j0 HJ HJ0.
(* 0x8274c lw a0,72(s6); 0x82750 bnez a0 *)
cw_run chk_awr. cw_keep cw_kwr_ro.
cw_branch Hbr.
all: rewrite branch_ne_U, (cw_U_sx32_eqb E 37 (kz_rc k mod 2 ^ 32) 0 E37 ltac:(lia) ltac:(lia)) in Hbr.
- (* k.rc <> 0: to LATCH *)
  cw_run_to chk_awr 0x8275c. cw_keep cw_kwr_ro.
  apply SRr_ret.
  lazymatch goal with
  | HS : st_ok tfibsegs ?Ev ?ssv (restrict (w_H _) ?msv), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msv) ?mdv _
    |- _ =>
    exact (chk_stop_at g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys Ev ssv msv mdv
      HJ0 Hfr Hk Hmo HC Hops Hcur Hkat HJ HAE HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) KE)
  end.
- (* k.rc = 0: 0x82754 mv a0,s6; jal check_bytes, returning to LATCH *)
  assert (Hrc0 : kz_rc k = 0).
  { apply (proj1 (chk_rc0 (kz_rc k) Wrc)). apply negb_false_iff in Hbr. apply Z.eqb_eq in Hbr. exact Hbr. }
  destruct (Hby Hrc0) as (B1 & B2' & B3 & B4 & B5).
  cw_run_to chk_awr 0x84640. cw_keep cw_kwr_ro.
  chk_do_call g pos sp1 ops c k ly2 S2 W2 regs2 mem2 md2 kev ys HJ0 Hfr Hk Hmo HC Hops Hcur Hkat UF
    (chk_byt_call g pos sp1 ops c k).
  + exact B1.
  + exact B2'.
  + exact B3.
  + exact B4.
  + exact B5.
Qed.

(* ================================ the segment ================================ *)
Theorem seg_chk_holds : seg_chk B MT K XM_LIB.
Proof using MTL TL LAWS ACR ACG ACB.
unfold seg_chk. intros g pos sp1 ops W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC & Hops &
  c & kc & od & Hcur & Hkat & Hrec & Hrc & Hwant).
destruct (amain_chk_facts kc od Hrec Hrc Hwant) as (P1 & P2 & P3 & P4).
assert (H0 : chk_at g pos sp1 ops c kc PC_CHK W2 (cfg_at tfibsegs PC_CHK regs2 mem2 md2)).
{ exists ly2, S2, regs2, mem2, md2, kev. split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfr|]. split; [exact Hk|]. split; [exact Hmo|]. split; [exact HC|].
  split; [exact Hops|]. split; [exact Hcur | exact Hkat]. }
eapply SRr_bind; [exact (chk_ph1 g pos sp1 ops c kc W2 _ H0 P1)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (chk_ph2 g pos sp1 ops c kc W3 c3 H3 P2 P3)|]. intros W4 c4 _ H4.
eapply SRr_mono; [exact (chk_ph3 g pos sp1 ops c kc W4 c4 H4 P4)|]. intros W5 c5 _ H5.
destruct H5 as (ly5 & S5 & regs5 & mem5 & md5 & k5 & -> & HJ5 & Hfr5 & Hk5 & Hmo5 & HC5 & Hops5 & Hcur5 & _).
exists ly5, S5, regs5, mem5, md5, k5. split; [reflexivity|].
split; [exact HJ5|]. split; [exact Hfr5|]. split; [exact Hk5|]. split; [exact Hmo5|]. split; [exact HC5|].
split; [exact Hops5 | exists c; exact Hcur5].
Qed.
End b.
End a.
