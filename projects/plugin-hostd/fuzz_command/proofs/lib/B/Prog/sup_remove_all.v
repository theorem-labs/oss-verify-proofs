(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_reply_code (plugin-hostd/fuzz_command, 0x89d6c, 20 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (pb_cmpPixel, a leaf that ends in a tail jump to a runtime entry) and A/ACh2.v (the step through a call and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_reply_code.v, with its module paths and module names changed; 167 of its 229 lines of code are new or changed and 226 lines of the source are left out. *)
(* The ASan+UBSan walk of sup_remove_all (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan,
   BASE + AF_sup_remove_all = 0x8b434, 10 instructions), in the form of a Theorem Labs lane's A walk re-fitted to statement
   passes 4 and 5 (lib/A/Prog/sup_remove_all_refit.v, a working branch e84227c9553): the executor over the position-abstract
   listing (lib/B/Prog/CmdPaLib.v), the call of record through the kit's cl_callS_pg (PaCallPg.v), and the tail
   jump `j answer` through sup_remove_all_s3.v's sra_tail.

   0x8b434 .. 0x8b43c (3 instructions): push the 16-byte frame, store ra at sp - 8, a0 := REC_REMOVE_ALL (3).
   0x8b440 `jal record`: record(3) records the call (REC_REMOVE_ALL, []) in the next slot of g_rec's table, or in
     record.spill after freeing the spill's old arguments, and returns the slot (record_c.v's trecord_spec, an
     apost_base post at the entry's FP state).
   0x8b444 .. 0x8b454 (5 instructions): a1 := the shape "resp 0" (PHi / PAddHi to A_OBJ 42 = 0x21d20), a2 := 1,
     reload ra, release the frame.
   0x8b458 `j answer`: answer(slot, "resp 0", 1) at the entry's sp (sra_tail; answer's post is apost_baseF).

   How B differs from A (55 instructions there): A inlines record() (the shadow-base load, the ncalls test, both
   arms with rec_calls_free, the two inline store4 checks and their error paths, s0 / s1 saved for it); B calls it
   (`li a0,3; jal record`), so this function has no branch, no inline shadow check, no static access and 0 UBSan
   trap sites (gen/traps.B.summary; the listing has no `unimp` in 0x8b434 .. 0x8b45c). Its symbolic state is one
   16-byte stack region (sup_remove_all_s4.v).

   The frame chain record's afn_pre asks at the call: s0 is the entry s0 (a Theorem Labs lane's S0-SITES.md class A), so it is
   afn_pre's chain kept above the entry sp (achain_kept: the run wrote only the frame) and lowered to the call's sp
   (achain_lower). The memory below the stack is the entry's at the call (the run's frame_of), so record's pre gets
   arodata_okP and the recorder's representation there (rec_repA_kept). After the call the frame word (ra) is kept:
   record's footprint lies below alloc_ceiling and its window below the frame.

   Walk hypotheses (a Theorem Labs lane's RULING-STMT.md §1): HB, LAWS, MTL, SIGP (two program-function transfers), IMG. Not
   taken: TL (no GOT word or shadow-base cell is read here), PRW (no static is written here), VHIS (no A_HI-based
   access: the PHi at 0x8b444 is consumed by its PAddHi), TLF / SMP / ASF / FFL / MTFL (no side-stack frame), ML. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaNoChain PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c answer_c sup_remove_all_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c hand_back_c rec_calls_free_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_remove_all_s1 sup_remove_all_s2 sup_remove_all_s3 sup_remove_all_s4.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Let TAILH := sra_tail B MT TANSWER HB LAWS MTL IMG.
Let RUN := paj_run B LAWS.

Ltac sra_awr WS Usp :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc fr ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_stack; [reflexivity | exact Usp | rewrite WS; cbn [YP09.r_wlo YP09.r_whi]; lia
      | cbn [YP09.r_wlo YP09.r_whi]; lia |] ].
Ltac sra_absmd :=
  repeat match goal with |- context [with_vm_backing ?l ?m ?d] =>
    let mdv := fresh "mdv" in set (mdv := with_vm_backing l m d) in *; clearbody mdv end.

Theorem tsup_remove_all_specF_holds : tsup_remove_all_specF B MT.
Proof.
unfold tsup_remove_all_specF.
intros ly S W regs mem md ch R O. cbv zeta.
intros HPRE HFRM HFR HROD HRO HREP HEV HLIVE HMO.
set (t := snd (sup_remove_all_m R)) in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : SUP_REMOVE_ALL_STK = ltac:(let v := eval vm_compute in SUP_REMOVE_ALL_STK in exact v)) by reflexivity.
assert (Hsp32 : alloc_ceiling + 16500 <= spZ regs) by (rewrite WS in Hslo; lia).
destruct (sra_entry B W ly S regs mem md ch HPRE) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_REMOVE_ALL_STK (sra_FP O) ly S W regs mem md ch HPRE) as HJ.
assert (V42 : VAL (A_OBJ 42) = 0x21d20) by (rewrite (VOBJS 42%nat ltac:(vm_compute; lia)); reflexivity).
assert (EL : forall k, (k < A_TEXT)%nat -> ew (sra_E regs) k = ew (Ereg regs sra_extra) k)
  by (intros k Hk; unfold sra_E; apply Eimg_low; exact Hk).
assert (HED : ed (sra_E regs) = ed (Ereg regs sra_extra)) by reflexivity.
assert (HEI : img_env VAL A_LIM (sra_E regs)) by (unfold sra_E; apply Eimg_env).
remember (sra_E regs) as E eqn:HE.
assert (EEo : forall k (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E8 : ew E 8 = getr regs 8) by (apply EEo; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 sra_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EOBJ' : forall i v, (13 <= i < 100)%nat -> VAL (A_OBJ i) = v -> 0 <= v < 2 ^ 64 -> ew E (A_OBJ i) = Z_to_bv 64 v).
{ intros i v Hi Hv Hr. apply bv_eq. rewrite (HEI (A_OBJ i) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Hv.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (E283 : ew E (A_OBJ 42) = Z_to_bv 64 0x21d20) by (apply EOBJ'; [lia | exact V42 | lia]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs sra_extra) E).
{ split; [intros k Hk; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
clear HE EL HED.
unfold cfg_at, w64.
(* 0x8b434 .. 0x8b43c: the frame, ra stored at sp - 8, a0 = 3; the run stops at the call of record *)
paj_run_tok RUN HS HJ SHOK sra_Bspan.
{ sra_awr WS Usp. }
sra_absmd.
(* the state at the call: sp = entry sp - 16, ra = BASE + 0x4f14 (0x8b444), a0 = REC_REMOVE_ALL = 3, s0 the entry's *)
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
assert (HspC : spZ (ms_regs ms) = spZ regs + -16).
{ unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
(* every byte outside the frame is the entry's: the run wrote only the frame's window *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem ss_sra) (w_H W) mem (ms_mem ms)
    (fun a => spZ regs - 16 <= a < spZ regs) HFr); [| exact Ha | exact Hn].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq | []].
  injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite Usp in Hrr. lia. }
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))).
{ intros a Hro Ho He.
  assert (Himg : in_img SEGS a)
    by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (CmdRecRo.RRO SEGS B LAWS HB IMG a Hr)]).
  pose proof (Hsegs a Himg). rewrite KEEP by lia. exact (HROD a Hro Ho He). }
assert (HOlive : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hp; exact (bsra_rep_live B _ _ _ _ _ pn HREP Hp)).
assert (HREPc : rec_repA B ly S (rdW W (ms_mem ms)) R O).
{ apply (rec_repA_kept B ly S (rdW W mem) ly S _ R O HREP HOlive).
  intros a Ha. apply KEEP.
  - destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
    destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hin & Hr).
    destruct (bsra_blk B LAWS ly S W mem md p n HAR (HOlive _ Hin)). lia.
  - destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
    destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hin & Hr).
    destruct (bsra_blk B LAWS ly S W mem md p n HAR (HOlive _ Hin)). lia. }
(* the frame chain at the call: s0 is the entry's, so afn_pre's chain, kept above the entry sp and lowered to the
   call's sp (a Theorem Labs lane's S0-SITES.md class A) *)
assert (HchC : achain ly (rdW W (ms_mem ms)) (spZ regs + -16) (s0Z (ms_regs ms)) ch).
{ assert (Es0 : s0Z (ms_regs ms) = s0Z regs) by (unfold s0Z; rewrite P8, E8; reflexivity).
  rewrite Es0. apply (achain_lower ly _ (spZ regs)); [|lia].
  apply (achain_kept ly (rdW W mem) (rdW W (ms_mem ms)) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. apply KEEP; lia. }
assert (HEVA : 0 <= EV_ANSWER) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HXA : 0 <= XM_ANSWER MT t).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length t) + 1) 1) ltac:(lia)). lia. }
pmkst HS.
rewrite (SIGP CS_record ltac:(unfold cmd_prog_syms; simpl; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_record) with AF_record by (vm_compute; reflexivity).
(* 0x8b440: record(REC_REMOVE_ALL), record's contract at the entry's FP state (record keeps it, apost_base) *)
eapply SRr_bind.
{ eapply (cl_callS_pg B LAWS W (ms_regs ms) (ms_mem ms) _ SUP_REMOVE_ALL_STK (spZ regs) (sra_FP O) ly S W mem md [] ly S
    mdv 0 RECORD_STK (sra_rec_FP R O) (EV_RECORD R) (-16) (Z_to_bv 64 (BASE + 20244)) ch).
  - exact HJ.
  - exact HspC.
  - reflexivity.
  - lia.
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply Z.leb_le. vm_compute. reflexivity.
  - rewrite P3, E3. exact Hgp.
  - rewrite P4, E4. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - exact HchC.
  - intros Hpre'. eapply SRr_mono.
    + apply (TRECORD fx ly S W (ms_regs ms) (ms_mem ms) mdv ch REC_REMOVE_ALL R O).
      * exact Hpre'.
      * exact HRODc.
      * exact P10.
      * unfold REC_REMOVE_ALL, REC_FN_COUNT. lia.
      * exact HREPc.
      * unfold EV_SUP_REMOVE_ALL in HEV. lia.
      * apply (mo_ok_le MT MTL S _ (XM_SUP_REMOVE_ALL MT R t) HMO). unfold XM_SUP_REMOVE_ALL. lia.
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & HQ2).
      exists ly2, S2, regs2, mem2, md2. rewrite P1 in Hc2. split; [exact Hc2|]. split; [exact HJ2|]. split; [exact HP2|].
      exact HQ2.
  - intros a Ha. left. exact (sra_rec_fp_cover B HB IMG ly S _ R O HREPc a Ha). }
clear SHOK. cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP2 & HK2).
(* back at 0x8b444: the frame (ra at sp - 8) is kept, since record's footprint lies below alloc_ceiling and its
   window below the frame *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?T -> _ => assert (HRK : T); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply G1; [unfold RECORD_STK, REC_CALLS_FREE_STK; lia | unfold RECORD_STK, REC_CALLS_FREE_STK; lia |].
    intros Hfp. pose proof (sra_rec_fp_low B LAWS HB IMG ly S W mem md _ R O HAR HREP a Hfp). lia.
  - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (A44 : ew (havoc E 40 (map (getr regs2) CLOB)) 44 = getr regs2 10) by reflexivity.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ec eqn:HEc.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDc : forall k, (k < 40)%nat -> ew Ec k = ew E k) by (intros k Hk; rewrite HEc; apply YN3v.ew_havoc_old; exact Hk).
assert (HAEc : env_agree 32 (Ereg regs sra_extra) Ec).
{ destruct HAE as [HA1 HA2]. split; [intros k Hk; rewrite OLDc by lia; exact (HA1 k Hk) | rewrite HEc; exact HA2]. }
assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by lia; exact Usp).
assert (Ec1 : ew Ec 1 = getr regs 1) by (rewrite OLDc by lia; exact E1).
assert (Ec283 : ew Ec (A_OBJ 42) = Z_to_bv 64 0x21d20).
{ change (A_OBJ 42) with 283%nat. rewrite HEc, ew_havoc_above by (cbv; lia). exact E283. }
clear HEc.
assert (SHOKc : sh_ok SEGS sra_Bx sra_SH0 Ec (mrestrict (w_H W2) mem2)) by (unfold sh_ok, sra_SH0; apply Forall_nil).
(* 0x8b444 .. 0x8b454: a1 = the shape "resp 0" (A_OBJ 42 = 0x21d20), a2 = 1, ra reloaded, the frame released; the
   run stops at the tail jump `j answer` *)
paj_run_tok RUN HS HJ2 SHOKc sra_Bspan.
{ sra_awr WS Uspc. }
sra_absmd.
(* at answer's entry: the registers *)
pose proof (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs sra_extra HS HAEc ltac:(vm_compute; reflexivity)) as HPT.
cbn [ms_regs restrict] in HPT.
prreg HS (1%bv : bv 5) T1. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
(* every byte below the stack is the post-call state's: the run wrote nothing *)
assert (KEEP2 : forall a, 0 <= a < alloc_ceiling -> rdW W2 (ms_mem ms0) a = rdW W2 mem2 a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) Ec _ (w_H W2) mem2 (ms_mem ms0)
    (fun a => spZ regs - 16 <= a < spZ regs) HFr0); [| lia | lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin as [Hq | []].
  injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite Uspc in Hrr. lia. }
destruct HK2 as (F & O1 & G10 & HPerm & _ & HFO & HREP1 & HO1 & HBB1 & MLE1).
assert (HREP1' : rec_repA B ly2 S2 (rdW W2 (ms_mem ms0)) (rec_record R REC_REMOVE_ALL []) O1).
{ pose proof HJ2 as (HAR2 & _).
  apply (rec_repA_kept B ly2 S2 (rdW W2 mem2) ly2 S2 _ _ O1 HREP1 (fun pn Hp => bsra_rep_live B _ _ _ _ _ pn HREP1 Hp)).
  intros a Ha. apply KEEP2.
  destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
  destruct (inFP_ablocks_fp_inv O1 a Ha) as (p & n & Hin & Hr).
  destruct (bsra_blk B LAWS ly2 S2 W2 (ms_mem ms0) mdv0 p n HAR2 (bsra_rep_live B _ _ _ _ _ _ HREP1 Hin)). lia. }
(* the tail jump: answer runs at the entry's sp *)
pmkst HS.
rewrite (SIGP CS_answer ltac:(unfold cmd_prog_syms; simpl; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_answer) with AF_answer by (vm_compute; reflexivity).
rewrite Z.add_0_l in HJ2.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
exact (TAILH ly S W regs mem md ch R O ly2 S2 W2 mT dT rT F O1
  HPRE HFRM HFR HROD HREP HEV HLIVE HMO HJ2 HPerm HFO HREP1' HO1 HBB1 MLE1 HPT
  ltac:(rewrite T1, Ec1; reflexivity) ltac:(rewrite T10, A44; exact G10)
  ltac:(rewrite T11; change (ew Ec 283%nat) with (ew Ec (A_OBJ 42)); rewrite Ec283; reflexivity)
  ltac:(rewrite T12; reflexivity)) end.
Qed.
(* the statement as a Theorem Labs lane states it: sra_FP and sra_post unfold to its footprint and post-condition *)
Theorem tsup_remove_all_spec_holds : tsup_remove_all_spec B MT.
Proof. exact tsup_remove_all_specF_holds. Qed.
End e.
End f.
End d.
