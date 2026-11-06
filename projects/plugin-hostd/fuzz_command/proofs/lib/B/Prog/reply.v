(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reply on the ASan+UBSan build of plugin-hostd/fuzz_command
   (fuzz_command.asan-ubsan; entry 0x8d9c4, 18 instructions), proving treply_spec (lib/B/Prog/reply_c.v) in
   cgif_file_fuzzer's walk style (A/ACh1.v..ACh8.v): the verified symbolic executor over the position-abstract
   listing (PaLibF's SRr_run_pi_AJ, PaCallRun's SRr_run_pi_AJ_call), the strlen wrapper through a Theorem Labs lane's contract and
   the kit's aj_art_at (PaArt.v), socket_send through its statement and the call rule (PaNoChain.v cl_callS_wide),
   and the tail jump into the free wrapper through cgif's afree04_rule (PaCall.v afree04_sub). reply has no inline
   check, no loop, no side-stack frame and no UBSan trap site (gen/traps.B.summary row `reply 0`).
   The B twin of lib/A/Prog/reply.v (a working branch 094fb7cf5be): B's 18 listing slots
   (lib/B/Prog/CmdList.v, AF_reply = 0x7494) are A's (AF_reply = 0x7a30) word for word except the pc-relative fields
   of the three calls; B pc = A pc - 0x550 (0x8df14 + k is 0x8d9c4 + k). The return address of the socket_send call
   is BASE + 0x74c4 (A BASE + 0x7a60). B's numbers: REPLY_STK = 32 + SOCKET_SEND_STK = 16480 (SOCKET_SEND_STK =
   48 + XMALLOC_STK = 16448: B's socket_send calls xmalloc). The statement's callee and runtime hypotheses are
   fx-generic (pass 4b); the walk applies them at fx.
   The record facts are a Theorem Labs lane's base lemmas over `SEGS B LAWS HB` (LAWS is YG0q.AR_laws_ok), each applied by
   exact: CmdRecImg.cmd_heap_tail_vis (the text's tail word), CmdRecImg.cmd_prog_unowned and CmdRecRo.relro_img
   (also over IMG : cmd_img_facts SEGS B). HB, TL, MTL and SIGP stay record hypotheses, as in A: no base lemma
   proves PALib, cmd_sig_prog of an abstract instance (CmdRecRest's cmd_palib / cmd_sig_prog_PB are at PB_cmd),
   or ameter_laws of an abstract meter.
   Re-fitted 2026-10-29 to the B wave a working branch f490061c104 (pass 5, a Theorem Labs lane's PASS4-REFIT.md): reply's
   post stays apost_base and socket_send's post is apost_base, so no call changes the FP state and the old closing
   stands (PASS4-REFIT.md A.3 step 4, first case); astack_pres is gone (section B): socket_send's chain at s0 = the
   text (a heap block) is achain_low, the free wrapper's chain_pre is achain_chain_pre on afn_pre's chain. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c socket_send_c reply_c reply_s1.
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
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (reply_c.v:65-68), fx-generic; the walk applies them at fx *)
Hypothesis SOCKET_SEND : forall fx0 : YK11.FPState, @tsocket_send_spec fx0 rc SK PI B MT.
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Hypothesis AFREE : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
(* the per-binary record hypotheses, with a Theorem Labs lane's names (a Theorem Labs lane's RULING-STMT.md §1); the record facts are the
   base lemmas of CmdRecImg / CmdRecRo over them (RULING-STMT.md §2.1) *)
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
(* SIGP (RULING-STMT.md §1): every program function's call target against the listing's base, CmdObj.v's
   cmd_sig_prog (a Definition, lib/B/Prog/CmdObj.v:44); the walk is parametric in PI, so it stays a premise *)
Hypothesis SIGP : cmd_sig_prog (PI := PI).
(* IMG (RULING-STMT.md §1): the image facts over the walk's abstract SEGS; the pinned image gives them
   (lib/B/Prog/CmdRecImg.v cmd_img_facts_tfib) *)
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
(* the interceptors' ROM premise (a Theorem Labs lane's rt_rom_view, lib/B/Rt/RtDefs.v) is the in-segment half of arodata_okP *)
Lemma rt_rom_of_aro : forall (W : world SEGS) mem, arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem.
Proof. intros W mem H a Ha Ho He. exact (H a (or_introl Ha) Ho He). Qed.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).
Lemma arodata_okP_img : forall rd rd', arodata_okP SEGS RLO RHI B rd -> (forall a, in_img SEGS a -> rd' a = rd a) ->
arodata_okP SEGS RLO RHI B rd'.
Proof.
intros rd rd' H Hk a Hro Ho He. rewrite Hk; [exact (H a Hro Ho He)|].
destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (CmdRecRo.relro_img SEGS B LAWS HB IMG a Hr)].
Qed.
Lemma astr_atR_some : forall (rd : reader) p s a, astr_atR rd p s -> p <= a < p + Z.of_nat (length s) + 1 -> rd a <> None.
Proof.
intros rd p s a [Hb _] Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (Hb (Z.to_nat (a - p))); [discriminate | rewrite length_app; cbn [length]; lia].
Qed.
Lemma blk_below : forall ly S (W : world SEGS) mem md p n k, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= k < n ->
4096 <= p /\ p + k < alloc_ceiling.
Proof.
intros ly S W mem md p n k HAR Hin Hk. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4 & Hc & _).
unfold req_size in Hc. destruct (Z.eqb_spec n 0); lia.
Qed.
Lemma addiw1_small : forall L, 0 <= L < 2 ^ 31 - 1 ->
sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 L)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (L + 1).
Proof.
intros L HL. rewrite zalu32_sound. f_equal. unfold zalu32. cbn [zalu_raw]. unfold zu32, M32, zcanon, M64.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ 32) with 4294967296. change (4294967296 / 2) with 2147483648.
rewrite (Z.mod_small L 4294967296) by lia. rewrite (Z.mod_small 1 4294967296) by lia.
rewrite (Z.mod_small (L + 1 + 2147483648) 4294967296) by lia.
replace (L + 1 + 2147483648 - 2147483648) with (L + 1) by lia. apply Z.mod_small. lia.
Qed.
(* the free wrapper removes one copy of the block from the list, and the live blocks are pairwise apart *)
Lemma blocks_rm_notin : forall ly S (W : world SEGS) mem md l1 l2 x, AR SEGS B ly S W mem md ->
ablocks B ly S = l1 ++ x :: l2 -> ~ In x (l1 ++ l2).
Proof.
intros ly S W mem md l1 l2 x HAR E Hin.
assert (Hx : In x (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct x as [p n].
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hx) as (_ & _ & _ & _ & _ & Hpw & Hn).
pose proof (req_size_pos n ltac:(lia)) as [Hr1 _].
rewrite E, map_app in Hpw. cbn [map] in Hpw.
apply in_app_or in Hin as [H | H]; apply in_split in H as (a & b & ->).
- rewrite map_app in Hpw. cbn [map] in Hpw. rewrite <- app_assoc in Hpw. cbn [app] in Hpw.
  pose proof (pairwise_In2 zdisjoint _ _ _ _ _ _ Hpw eq_refl) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
- rewrite map_app in Hpw. cbn [map] in Hpw.
  pose proof (pairwise_In2 zdisjoint _ _ _ _ _ _ Hpw eq_refl) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Theorem treply_proof : treply_spec B MT.
Proof.
unfold treply_spec. intros ly S W regs mem md ch q nq X R O HPRE HROD H11 Hq64 Hin HnO Hap HSTR HLn HL4096 HREC HNR Hev Hlive HMOK.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : REPLY_STK = 16480) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HSS : SOCKET_SEND_STK = 16448) by reflexivity.
assert (HL0 : 0 <= Z.of_nat (length X)) by lia.
set (L := Z.of_nat (length X)) in *.
set (FP := (A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp ((q, nq) :: O)).
pose proof (ajournal_init SEGS B REPLY_STK FP ly S W regs mem md ch HPRE) as HJ.
set (sp0 := spZ regs) in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q nq HAR Hin) as (Hq16 & Hq4096 & Hqceil & _).
pose proof (req_size_pos nq ltac:(lia)) as [Hrs1 Hrs2].
(* the text's tail word (the strlen wrapper's musl loop reads past the terminator to the end of its 8-byte word) *)
pose proof (CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md q nq (q + L) HAR Hin ltac:(lia)) as HTV.
assert (HOb : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ HREC Hpn)).
assert (HFPlo : forall a, inFP FP a -> a < alloc_ceiling).
{ intros a (r & Hr & Ha). destruct Hr as [<- | Hr]; [cbn in Ha; unfold A_G_REC, REC_SIZE in Ha; lia|].
  apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn [fst snd] in Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (ltac:(destruct Hpn as [Hpn | Hpn]; [injection Hpn as <- <-; exact Hin | exact (HOb _ Hpn)]))) as (_ & _ & Hc & _). lia. }
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E (mkSS AF_reply sr_atoms [stack_region 32] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reply)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, stack_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
unfold cfg_at. change (w64 (BASE + AF_reply)) with (Z_to_bv 64 (BASE + AF_reply)).
(* 0x8d9c4 .. 0x8d9e0: the frame, the spills of ra, s0, s1, and the call of the strlen wrapper *)
paj_run_shc RUNP RUNC HS HJ.
{ eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn; lia | cbn; lia | apply awr_ok_nil]. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 32 <= a < sp0) HFr
  ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin'; destruct Hin' as [Hq | []]; injection Hq as <- <- <-;
        cbn [base_val] in Hrr; rewrite Usp in Hrr; lia)) as UN1.
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10.
assert (Qsp : spZ (ms_regs ms) = sp0 + -32) by (unfold spZ; rewrite Q2, Usp; rewrite unsigned_lit_small by lia; lia).
pmkst HS.
assert (HRO1 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))).
{ apply (arodata_okP_img _ _ HROD). intros a Ha. pose proof (pa_img_range a Ha). apply UN1; lia. }
pose proof (proj1 HJ) as HAR1.
pose proof (ecall_pre_stk_at SEGS B ESTACK REPLY_STK sp0 FP ly S W mem md [] ly S W (ms_mem ms) _ 0 (ms_regs ms) (-32) HJ
  Qsp eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
  ltac:(rewrite Q3, (EE 3%nat 3%bv eq_refl); exact Hgp) ltac:(rewrite Q4, (EE 4%nat 4%bv eq_refl); exact Htp)) as HPRE1.
eapply SRr_bind.
{ eapply (ART ESTACK (fun _ => False) _ W (ms_regs ms) (ms_mem ms) REPLY_STK sp0 FP ly S W mem md [] ly S _ 0 (-32) _
    (fun regs' _ => getr regs' 10 = w64 (astr_len X)) HJ);
  [exact Qsp | reflexivity | lia | lia | lia | exact Q1 | intros a [] |].
  apply (STRLEN fx ly S W _ _ _ q X HPRE1).
  - rewrite Q10, (EE 11%nat 11%bv eq_refl). exact H11.
  - lia.
  - apply (proj1 (astr_atR_view SEGS W (ms_mem ms) q X)). apply (astr_atR_agree _ _ q X (L + 1) HSTR); [lia|].
    intros k Hk. apply UN1; lia.
  - change (astr_len X) with L. unfold aread_ok.
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [intros a Ha; split; [rewrite UN1 by lia; exact (astr_atR_some _ q X a HSTR ltac:(lia)) | unfold ascratch_stk; rewrite Qsp; lia]|].
    split; [exact (amem_range_of_block SEGS B LAWS _ _ _ _ _ q nq q (L + 1) HAR Hin ltac:(lia) ltac:(lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ q nq q (L + 1) HAR1 Hin ltac:(lia) ltac:(lia))|].
    intros _. exact (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ q nq q (L + 1) HAR1 Hin ltac:(lia) ltac:(lia) ltac:(lia)).
  - change (astr_len X) with L. intros a Ha. pose proof (Z.mod_pos_bound (q + L) 8 ltac:(lia)). rewrite UN1 by lia. apply HTV. exact Ha.
  - apply rt_rom_of_aro. exact HRO1. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2').
pose proof (fun a Ha Hn => HK2' a Ha Hn (fun x : False => x)) as HK2. clear HK2' HPRE1.
change (astr_len X) with L in Ha02.
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2.
lazymatch type of HS2 with ?P -> _ => assert (HQ : P); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply HK2; lia.
  - intros _. apply (apresent_writable SEGS). apply Hpres2. lia. }
rewrite <- restrict_mkst_fx in HS2.
pose proof (img_env_havoc_hi E 1024 (map (getr regs2) CLOB) HEI ltac:(unfold A_LIM; lia)) as HEI2.
assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 4128 <= a < sp0) -> rdW W mem2 a = rdW W mem a)
  by (intros a Ha Hna; rewrite HK2 by lia; apply UN1; lia).
clear UN1 HK2 HS Q1 Q2 Q3 Q4 Q10 Qsp.
(* 0x8d9e4 .. 0x8d9f0: size = (int)(strlen + 1), the call of socket_send(fd, text, size) *)
paj_run_shc RUNP RUNC HS2 HJ2.
{ eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | rewrite ew_havoc_old by (cbn; lia); exact Usp | cbn; lia | cbn; lia | apply awr_ok_nil]. }
prreg HS2 (1%bv : bv 5) Q1. prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4.
prreg HS2 (8%bv : bv 5) Q8. prreg HS2 (11%bv : bv 5) Q11. prreg HS2 (12%bv : bv 5) Q12.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 32 <= a < sp0) HFr
  ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin'; destruct Hin' as [Hq | []]; injection Hq as <- <- <-;
        cbn [base_val] in Hrr; rewrite ew_havoc_old, Usp in Hrr by (cbn; lia); lia)) as UN3'.
assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 4128 <= a < sp0) -> rdW W (ms_mem ms0) a = rdW W mem a)
  by (intros a Ha Hna; rewrite UN3' by lia; apply UN2; lia).
clear HF HFr HG UN3'.
assert (Qsp : spZ (ms_regs ms0) = sp0 + -32) by (unfold spZ; rewrite Q2, Usp; rewrite unsigned_lit_small by lia; lia).
assert (Q12' : getr (ms_regs ms0) 12 = w64 (L + 1)).
{ rewrite Q12. change (nth 4 (map (getr regs2) CLOB) (ew E 1028)) with (getr regs2 10). rewrite Ha02. unfold w64.
  apply addiw1_small. lia. }
assert (Q11' : getr (ms_regs ms0) 11 = w64 q) by (rewrite Q11, (EE 11%nat 11%bv eq_refl); exact H11).
assert (Q8' : getr (ms_regs ms0) 8 = w64 q) by (rewrite Q8, (EE 11%nat 11%bv eq_refl); exact H11).
pmkst HS2.
pose proof (proj1 HJ2) as HAR3.
assert (HRO3 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms0))).
{ apply (arodata_okP_img _ _ HROD). intros a Ha. pose proof (pa_img_range a Ha). apply UN3; lia. }
assert (HREC3 : rec_repA B ly S (rdW W (ms_mem ms0)) R O).
{ apply (rec_repA_agree B _ _ _ _ _ _ R O HREC (fun pn _ Hb => Hb)).
  - intros k Hk. apply UN3; unfold A_G_REC, REC_SIZE in *; lia.
  - intros k Hk. apply UN3; unfold A_REC_SPILL, SC_SIZE in *; lia.
  - intros [p n] Hpn k Hk. cbn [fst snd] in *. pose proof (blk_below _ _ _ _ _ p n k HAR (HOb _ Hpn) Hk). apply UN3; lia. }
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms0) (ms_mem ms0) _ REPLY_STK sp0 FP ly S W mem md [] ly S _ 0 SOCKET_SEND_STK
    ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) EV_SOCKET_SEND (-32) (Z_to_bv 64 (BASE + 29892)) []
    (fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
       getr regs' 10 = w64 (L + 1) /\
       rec_repA B ly' S' (rdW W' mem') (fst (socket_send_m R (X ++ [Z_to_bv 8 0]))) O' /\
       (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
       (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
       (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
       blocks_bytes S' <= blocks_bytes S + LIVE_SOCKET_SEND /\
       mo_le MT S S' (XM_SOCKET_SEND MT (L + 1))) HJ2).
  - exact Qsp.
  - reflexivity. - lia. - lia. - lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite Q8'. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1.
    rewrite (SIGP CS_socket_send) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
    change (cmd_af CS_socket_send) with AF_socket_send. eapply SRr_mono.
    { apply (SOCKET_SEND fx ly S W (ms_regs ms0) (ms_mem ms0) _ [] q (L + 1) (X ++ [Z_to_bv 8 0]) R O HPRE1 HRO3 Q11' Hq64
        Q12' ltac:(lia) HREC3 HNR).
      - intros _. split; [unfold LMAX; lia|]. split; [rewrite length_app, Nat2Z.inj_add; change (Z.of_nat (length X)) with L; cbn; lia|].
        split; [apply (abytes_atR_agree _ _ q _ (L + 1) (proj1 HSTR)); [rewrite length_app, Nat2Z.inj_add; change (Z.of_nat (length X)) with L; cbn; lia | intros k Hk; apply UN3; lia]|].
        split; [exists q, nq; split; [exact Hin | lia] | exact Hap].
      - intros Hle. lia.
      - unfold EV_REPLY in Hev. lia.
      - unfold LIVE_REPLY in Hlive. exact Hlive.
      - apply (mo_ok_le MT MTL S _ (XM_REPLY MT (L + 1)) HMOK). unfold XM_REPLY. pose proof (mo_free_nonneg MT MTL). lia. }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. rewrite Q1. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - (* the callee's footprint: g_rec, a program static of the image the caller's footprint holds, and the recorder's
       blocks *)
    intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
    + right; right; right; right; left.
      split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | exact Ha]|].
      split; [rewrite (YF0m.ts_prog B HB); unfold YF0m.TFIB_PROG_STATIC; apply Exists_cons_hd;
              unfold in_zr; cbn [fst snd]; unfold A_G_REC, REC_SIZE in Ha; lia|].
      apply (CmdRecImg.cmd_prog_unowned SEGS B LAWS HB IMG a). unfold cmd_PG. apply inFP_cons. left. exact Ha.
    + destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hpn & Hr). destruct Ha as (r & Hr' & Hrr).
      right; left. split; [exists r; split; [right; right; exact Hr' | exact Hrr]|].
      exists p, n. split; [exact (HOb _ Hpn) | exact Hr].
  - (* no footprint byte lies in reply's stack window: the footprint is below alloc_ceiling *)
    intros ? ? ? ? ? ? _ a Ha Hw _. exfalso.
    assert (HFa : inFP FP a).
    { apply inFP_cons in Ha as [Ha | (r & Hr & Hrr)];
      [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | exact Ha]
      | exists r; split; [right; right; exact Hr | exact Hrr]]. }
    pose proof (HFPlo a HFa). lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & (O' & Ha03 & HRECs & HO'1 & HO'2 & HO'3 & HBB3 & HMLE3)).
assert (HqO' : ~ In (q, nq) O') by (intros H; destruct (HO'1 _ H) as [H' | H']; [exact (HnO H') | exact (H' Hin)]).
jafter_call_keep_hi HS2 1040%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0%nat] HS3.
lazymatch type of HS3 with ?P -> _ => assert (HQ : P); [| specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply region_kept_stack_sub; [exact HJc3 | exact HJ3 | rewrite ew_havoc_old by (cbn; lia); exact Usp | lia | lia | lia | lia | lia |].
  intros a Ha (r & Hr & Hrr). assert (HFa : inFP FP a).
  { exists r. split; [destruct Hr as [<- | Hr]; [left; reflexivity | right; right; exact Hr] | exact Hrr]. }
  pose proof (HFPlo a HFa). lia. }
rewrite <- restrict_mkst_fx in HS3.
pose proof (img_env_havoc_hi _ 1040 (map (getr regs3) CLOB) HEI2 ltac:(unfold A_LIM; lia)) as HEI3.
clear HS2 HJ2 HJc3 Q1 Q2 Q3 Q4 Q8 Q11 Q12 Q12' Q11' Q8' Qsp HRO3 HREC3 HAR3 UN2 UN3.
(* 0x8d9f4 .. 0x8da08: a0 = text, the frame popped, the tail jump into the free wrapper *)
paj_run_shc RUNP RUNC HS3 HJ3.
{ eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | rewrite !ew_havoc_old by (cbn; lia); exact Usp | cbn; lia | cbn; lia | apply awr_ok_nil]. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 32 <= a < sp0) HFr
  ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin'; destruct Hin' as [Hq | []]; injection Hq as <- <- <-;
        cbn [base_val] in Hrr; rewrite !ew_havoc_old, Usp in Hrr by (cbn; lia); lia)) as UN4.
clear HF HFr HG.
prreg HS3 (1%bv : bv 5) R1. prreg HS3 (2%bv : bv 5) R2. prreg HS3 (3%bv : bv 5) R3. prreg HS3 (4%bv : bv 5) R4.
prreg HS3 (8%bv : bv 5) R8. prreg HS3 (10%bv : bv 5) R10.
(* the callee-saved registers are back at their entry values: the restores at 0x8d9f8 .. 0x8da04, and the two calls *)
assert (HPT : aregs_preserved regs (ms_regs ms1)).
{ apply aregs_preserved_eqs;
  (rewrite (st_ok_restrict_reg SEGS _ _ _ _ _ HS3); cbn [ms_regs];
   lazymatch goal with |- sv_denot _ (sr_get ?a ?rr) = _ => let v := eval vm_compute in (sr_get a rr) in change (sr_get a rr) with v end;
   cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?ew_havoc_old by (cbn; lia);
   lazymatch goal with |- ew _ ?n = getr _ ?r => apply (EE n r); reflexivity end). }
assert (R1' : getr (ms_regs ms1) 1 = getr regs 1) by (rewrite R1; exact (EE 1%nat 1%bv eq_refl)).
assert (R3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite R3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (R4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite R4, (EE 4%nat 4%bv eq_refl); exact Htp).
assert (R10' : getr (ms_regs ms1) 10 = w64 q) by (rewrite R10, (EE 11%nat 11%bv eq_refl); exact H11).
assert (RsT : spZ (ms_regs ms1) = sp0 + 0) by (unfold spZ; rewrite R2, Usp; lia).
pose proof (proj1 HJ3) as HAR4.
pose proof HJ3 as (_ & Hly3 & _ & _ & _ & _ & Hnev3 & _ & F13 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
assert (Hq3 : In (q, nq) (ablocks B ly3 S3)) by exact (HO'3 _ Hin HnO).
assert (Hach : achain ly3 (rdW W3 (ms_mem ms1)) sp0 (s0Z regs) ch).
{ apply (achain_ly_top ly ly3); [exact Etop3 |].
  apply (achain_kept ly (rdW W mem) _ sp0 (s0Z regs) ch sp0 Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply F13; [lia | lia | intros Hf; pose proof (HFPlo a Hf); lia]. }
assert (Hchp : chain_pre ly3 (rdW W3 (ms_mem ms1)) (ms_regs ms1) ch).
{ apply (achain_chain_pre ly3 _ sp0 (s0Z regs) ch (ms_regs ms1) Hach).
  - rewrite RsT. lia.
  - unfold s0Z. rewrite R8, (EE 8%nat 8%bv eq_refl). reflexivity.
  - unfold raZ in *. rewrite R1'. exact Hra4. }
assert (Hnev' : st_nev S3 < EV_MAX) by (unfold EV_REPLY, EV_SOCKET_SEND in *; lia).
assert (HMOKf : mo_ok MT S3 (mo_free MT)) by exact (mo_ok_step MT MTL S S3 (XM_SOCKET_SEND MT (L + 1)) (mo_free MT) HMOK HMLE3).
assert (Hcov : In (q, nq) (ablocks B ly S) -> forall i, 0 <= i < req_size nq -> inFP FP (q + i)).
{ intros _ i Hi. exists (q, q + req_size nq). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
pmkst HS3. rewrite (pal_free B TL).
eapply SRr_mono.
{ exact (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE fx) W3 (ms_regs ms1) (ms_mem ms1) REPLY_STK sp0 FP ly S W mem md [] ly3 S3 _
    (0 + EV_SOCKET_SEND) q nq 0 (getr regs 1) ch HJ3 Hq3 R10' RsT eq_refl ltac:(lia) ltac:(unfold ASTACK; lia) R3' R4' R1' Hra Hnev' Hchp
    Hcov HMOKf). }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & E3b & E4b) & Hfr4 & HK4 & HMLE4 & HJf4).
assert (HEVR' : EV_REPLY = 0 + EV_SOCKET_SEND + 1) by reflexivity.
unfold apost_base. exists ly4, S4, regs4, mem4, md4. split; [reflexivity|].
split; [rewrite HEVR'; exact HJ4|].
split; [exact (aregs_preserved_trans _ _ _ HPT HP4)|].
assert (Hnot : ~ In (q, nq) (l1 ++ l2)) by exact (blocks_rm_notin _ _ _ _ _ l1 l2 (q, nq) HAR4 E3b).
assert (HO'b : forall pn, In pn O' -> In pn (ablocks B ly3 S3)) by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ HRECs Hpn)).
assert (Hrm : forall pn, In pn (ablocks B ly3 S3) -> pn <> (q, nq) -> In pn (ablocks B ly4 S4)).
{ intros pn Hpn Hne. rewrite E4b. rewrite E3b in Hpn. apply in_or_app.
  apply in_app_or in Hpn as [H | [H | H]]; [left; exact H | congruence | right; exact H]. }
pose proof HK4 as (_ & K2 & K3 & _).
exists O'. split.
{ (* the recorder after socket_send, past the free of the text: g_rec, record.spill and the new reply block are
     apart from the text block and from the free wrapper's window *)
  apply (rec_repA_agree B _ _ _ _ (rdW W3 mem3) _ _ O' HRECs).
  - intros pn Hpn Hb. apply Hrm; [exact Hb | intros ->; exact (HqO' Hpn)].
  - intros k Hk. assert (Hpg : inFP cmd_PG (A_G_REC + k)) by (unfold cmd_PG; apply inFP_cons; left; unfold REC_SIZE in Hk; lia).
    destruct (CmdRecImg.cmd_prog_unowned SEGS B LAWS HB IMG _ Hpg) as (Himg & Hown & Herr). pose proof (pa_img_range _ Himg).
    rewrite (K3 _ Himg Hown Herr). apply UN4; lia.
  - intros k Hk. assert (Hpg : inFP cmd_PG (A_REC_SPILL + k))
      by (unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; left; unfold SC_SIZE in Hk; unfold A_REC_SPILL; lia).
    destruct (CmdRecImg.cmd_prog_unowned SEGS B LAWS HB IMG _ Hpg) as (Himg & Hown & Herr). pose proof (pa_img_range _ Himg).
    rewrite (K3 _ Himg Hown Herr). apply UN4; lia.
  - intros [p n] Hpn k Hk. cbn [fst snd] in *. pose proof (HO'b _ Hpn) as Hb.
    assert (Hne : (p, n) <> (q, nq)) by (intros E'; rewrite E' in Hpn; exact (HqO' Hpn)).
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ p n q nq HAR4 Hb Hq3 Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D.
    pose proof (blk_below _ _ _ _ _ p n k HAR4 Hb Hk) as [Hp4 Hpk].
    pose proof (req_size_pos n ltac:(lia)) as [_ Hrn].
    rewrite (K2 p n k Hb ltac:(lia) ltac:(lia)). apply UN4; lia. }
split; [rewrite E4b; exact Hnot|].
split; [intros pn Hpn HnOp Hne; exact (Hrm _ (HO'3 _ Hpn HnOp) Hne)|].
split.
{ intros pn Hpn. rewrite E4b in Hpn.
  assert (Hpn3 : In pn (ablocks B ly3 S3)) by (rewrite E3b; apply in_or_app; apply in_app_or in Hpn as [H | H]; [left; exact H | right; right; exact H]).
  assert (Hne : pn <> (q, nq)) by (intros ->; exact (Hnot Hpn)).
  destruct (HO'2 _ Hpn3) as [[H1 H2] | H]; [left; split; [exact H1 | split; [exact H2 | exact Hne]] | right; exact H]. }
split; [exact HO'1|].
split.
{ (* the live bytes: socket_send's bound, and the free removes the text block (YCbq.v blocks_bytes_bsum) *)
  assert (BB : forall ly0 S0, blocks_bytes S0 = bsum (ablocks B ly0 S0)) by (exact (blocks_bytes_bsum B)).
  rewrite (BB ly3 S3), E3b, bsum_app, bsum_cons in HBB3. cbn [snd] in HBB3.
  rewrite (BB ly4 S4), E4b, bsum_app. unfold LIVE_REPLY. lia. }
exact (mo_le_trans MT MTL _ _ _ _ _ HMLE3 HMLE4).
Qed.
End e.
End f.
End d.
