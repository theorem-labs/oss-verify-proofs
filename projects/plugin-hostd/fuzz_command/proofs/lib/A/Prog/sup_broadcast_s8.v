(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the spill arm of plugin-hostd/fuzz_command's sup_broadcast walk (0x8afa0 ..
   0x8afe8 with g_rec.ncalls = 16): the head saves ra/s0/s1/s2 in the 32-byte frame, reads ncalls, takes the spill
   arm and calls rec_calls_free(record.spill, 1), which frees the spill's arguments; the store block follows at
   0x8afec (sup_broadcast_s5.v's sb_store).
   Pass-4/5 re-fit: rec_calls_free keeps the FP state (its post is apost_base), so its call
   keeps the kit's cl_callS_wide with TREC_CALLS_FREE at the entry's fx; the arm ends at apost_baseF and passes the
   rounding-mode-0 premise HFRM on to sb_store. Statement pass 5 removed astack_pres from both pres; the frame chain
   at the call is achain's empty case (s0 = line, a heap pointer below alloc_ceiling). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_canonical_c xstrdup_c hand_back_c rec_calls_free_c arg_line_c answer_c sup_broadcast_c PaNoChain sup_broadcast_s1 sup_broadcast_s2
sup_broadcast_s3 sup_broadcast_s4 sup_broadcast_s5 sup_broadcast_s6.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a.
Hypothesis cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a.
Hypothesis cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS.

(* the call target of rec_calls_free *)
Lemma sb8_sig_rcf : SIGMA CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof. rewrite (SIGP CS_rec_calls_free); [reflexivity | cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right])]. Qed.

(* rec_calls_free's footprint for record.spill: the spill's nargs field and the blocks of its arguments *)
Lemma sb8_fp1 : forall (P : list (Z * Z)) a, inFP (rcf_fp A_REC_SPILL [P]) a ->
(A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) \/
exists b m, In (b, m) P /\ b <= a < b + req_size m.
Proof.
intros P a Ha. unfold rcf_fp in Ha. cbn [length seq map concat] in Ha. rewrite app_nil_r in Ha.
apply inFP_app in Ha as [Ha | Ha].
- apply inFP_cons in Ha as [Ha | Ha]; [left; unfold CALL_SIZE in Ha; lia | exfalso; exact (inFP_nil a Ha)].
- right. exact (inFP_ablocks_fp_inv P a Ha).
Qed.

(* sbe_entry's state has no fact for g_rec's atom, so cells_safe_b rejects the write window of sbe_ncalls; the run
   starts from the state with g_rec's fact added *)
Lemma sb8_add_atom : forall E ss ms n f, st_ok_pi SEGS VAL E ss ms -> afact_ok E n f ->
st_ok_pi SEGS VAL E (YP06.add_atom ss n f) ms.
Proof.
intros E [pc sr fr rs rv G] ms n f HS Hf.
unfold st_ok_pi, abs_ss, YP06.add_atom in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 _)))))))).
apply YP06.facts_ok_add_atom; assumption.
Qed.

(* the frame after the head (0x8afa0 .. 0x8afd0, as sup_broadcast_s7.v's sbh_stack) *)
Definition sb8_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0
[YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
 YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

(* the head with the spill arm, from the entry to the call of rec_calls_free at 0x8afe8 (ncalls = 16: the bne is
   decided); the facts at the call go to the continuation HK *)
Lemma sb8_reach : forall ly S W regs mem md ch O (Qk : world SEGS -> config -> Prop),
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 16 ->
(forall regsP memP mdP,
 ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly S W memP mdP 0 ->
 spZ regsP = spZ regs - 32 ->
 getr regsP 1 = Z_to_bv 64 (BASE + SB_RET_RCF) ->
 getr regsP 8 = getr regs 10 ->
 getr regsP 9 = w64 A_REC_SPILL -> getr regsP 10 = w64 A_REC_SPILL -> getr regsP 11 = w64 1 ->
 getr regsP 18 = Z_to_bv 64 SB_SB ->
 (forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr regsP (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 aval_mem (rdW W memP) (spZ regs - 8) 8 (raZ regs) -> aval_mem (rdW W memP) (spZ regs - 16) 8 (s0Z regs) ->
 aval_mem (rdW W memP) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
 aval_mem (rdW W memP) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W memP a = rdW W mem a) ->
 aval_mem (rdW W memP) (A_G_REC + OFF_NCALLS) 4 16 ->
 SRr SEGS W (mkCfg (mkst regsP (Z_to_bv 64 (SIGMA CS_rec_calls_free)) memP (seg_rom SEGS)) mdP) Qk) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_broadcast) regs mem md) Qk.
Proof.
intros ly S W regs mem md ch O Qk HPRE Hn HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WSTK : SUP_BROADCAST_STK = 16592) by reflexivity.
destruct (sbe_obj VOBJS) as (Vgrec & Vspill & _ & _).
destruct (sbe_entry B HB LAWS TL VOBJS PRW ly S W regs mem md ch 16 HPRE Hn ltac:(lia)) as [HS0 SHOK].
pose proof (ajournal_init SEGS B SUP_BROADCAST_STK (sb_FP O) ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs sbe_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros k r Hk. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E32 : ew E 32 = Z_to_bv 64 SB_SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Ugrec : bv_unsigned (ew E SB_GREC) = A_G_REC).
{ subst E. rewrite Eimg_img by (unfold SB_GREC, A_OBJ, A_TEXT, A_LIM; lia). rewrite Vgrec.
  apply unsigned_lit_small. unfold A_G_REC; lia. }
assert (Ugrec285 : bv_unsigned (ew E 285%nat) = A_G_REC) by exact Ugrec.
assert (ESP : ew E SB_SPILL = w64 A_REC_SPILL).
{ subst E. rewrite Eimg_img by (unfold SB_SPILL, A_OBJ, A_TEXT, A_LIM; lia). rewrite Vspill. reflexivity. }
assert (ESP292 : ew E 292%nat = w64 A_REC_SPILL) by exact ESP.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E (YP06.add_atom (ss_sbe 16) SB_GREC (mkAF A_G_REC A_G_REC 3))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_broadcast)) mem (seg_rom SEGS)))).
{ apply sb8_add_atom; [exact HS0|]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ugrec.
  split; [lia|]. split; [reflexivity | lia]. }
clear HS0 HE.
unfold cfg_at. change (w64 (BASE + AF_sup_broadcast)) with (Z_to_bv 64 (BASE + AF_sup_broadcast)).
paj_run_tok RUN HS HJ SHOK sbe_Bspan.
{ awr_ok_tac;
  first
  [ exact Usp
  | eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 285%nat A_G_REC); [reflexivity | exact Ugrec285 | | apply awr_ok_nil];
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
    assert (Hpg : inFP cmd_PG a) by (exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; lia]);
    unfold awr_byte, awr_prog_or_caller; do 4 right; left;
    split; [unfold sb_FP; apply inFP_cons; left; unfold OFF_NCALLS; lia | split; [exact (HPROG B HB a Hpg) | exact (cif_prog_img a Hpg)]] ]. }
pmkst HS.
lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv := with_vm_backing x y z) in *; clearbody mdv end.
prreg HS (1%bv : bv 5) P1; prreg HS (2%bv : bv 5) P2; prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9;
prreg HS (10%bv : bv 5) P10; prreg HS (11%bv : bv 5) P11; prreg HS (18%bv : bv 5) P18;
prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
prreg HS (19%bv : bv 5) P19; prreg HS (20%bv : bv 5) P20; prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22;
prreg HS (23%bv : bv 5) P23; prreg HS (24%bv : bv 5) P24; prreg HS (25%bv : bv 5) P25; prreg HS (26%bv : bv 5) P26;
prreg HS (27%bv : bv 5) P27.
pose proof HS as HSo. unfold st_ok_pi in HSo.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W (ms_mem ms) a = rdW W mem a) by
 (intros a Ha H1 H2; apply (kept_of_frame (segs:=SEGS) E _ (w_H W) mem (ms_mem ms)
    (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) HFr);
  [ intros b wlo whi a' Hin Hr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Ugrec285, ?Usp in Hr; cbv beta; unfold OFF_NCALLS; lia|]);
    destruct Hin
  | exact Ha | cbv beta; intros [Hc | Hc]; [exact (H1 Hc) | exact (H2 Hc)] ]).
assert (Vs2 : aval_mem (rdW W (ms_mem ms)) (spZ regs - 32) 8 (bv_unsigned (getr regs 18))) by
 (apply sb_aval_of_val_mem;
  replace (spZ regs - 32) with (base_val E (YP09.r_base sb8_stack) + -32) by (cbn [YP09.r_base base_val sb8_stack]; rewrite Usp; lia);
  apply (sb_chunk_val (w_H W) E _ ms 0%nat sb8_stack 0%nat (-32) 8 (SOff 18 0) (bv_unsigned (getr regs 18)) HSo);
  [ vm_compute; reflexivity | vm_compute; reflexivity
  | cbn [sv_denot]; rewrite Z.add_0_r, (EE 18%nat 18%bv eq_refl); reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr regs 18))
  | cbn; lia ]).
assert (Vs1 : aval_mem (rdW W (ms_mem ms)) (spZ regs - 24) 8 (bv_unsigned (getr regs 9))) by
 (apply sb_aval_of_val_mem;
  replace (spZ regs - 24) with (base_val E (YP09.r_base sb8_stack) + -24) by (cbn [YP09.r_base base_val sb8_stack]; rewrite Usp; lia);
  apply (sb_chunk_val (w_H W) E _ ms 0%nat sb8_stack 1%nat (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) HSo);
  [ vm_compute; reflexivity | vm_compute; reflexivity
  | cbn [sv_denot]; rewrite Z.add_0_r, (EE 9%nat 9%bv eq_refl); reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr regs 9))
  | cbn; lia ]).
assert (Vs0 : aval_mem (rdW W (ms_mem ms)) (spZ regs - 16) 8 (s0Z regs)) by
 (apply sb_aval_of_val_mem;
  replace (spZ regs - 16) with (base_val E (YP09.r_base sb8_stack) + -16) by (cbn [YP09.r_base base_val sb8_stack]; rewrite Usp; lia);
  apply (sb_chunk_val (w_H W) E _ ms 0%nat sb8_stack 2%nat (-16) 8 (SOff 8 0) (s0Z regs) HSo);
  [ vm_compute; reflexivity | vm_compute; reflexivity
  | cbn [sv_denot]; rewrite Z.add_0_r, (EE 8%nat 8%bv eq_refl); reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr regs 8))
  | cbn; lia ]).
assert (Vra : aval_mem (rdW W (ms_mem ms)) (spZ regs - 8) 8 (raZ regs)) by
 (apply sb_aval_of_val_mem;
  replace (spZ regs - 8) with (base_val E (YP09.r_base sb8_stack) + -8) by (cbn [YP09.r_base base_val sb8_stack]; rewrite Usp; lia);
  apply (sb_chunk_val (w_H W) E _ ms 0%nat sb8_stack 3%nat (-8) 8 (SOff 1 0) (raZ regs) HSo);
  [ vm_compute; reflexivity | vm_compute; reflexivity
  | cbn [sv_denot]; rewrite Z.add_0_r, (EE 1%nat 1%bv eq_refl); reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr regs 1))
  | cbn; lia ]).
assert (VNC : aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4 16) by
 (apply sb_aval_of_val_mem;
  replace (A_G_REC + OFF_NCALLS) with (base_val E (YP09.r_base (sbe_ncalls 16)) + 8)
    by (cbn [YP09.r_base base_val sbe_ncalls]; rewrite Ugrec; reflexivity);
  apply (sb_chunk_val (w_H W) E _ ms 3%nat (sbe_ncalls 16) 0%nat 8 4 (SLit 16) 16 HSo);
  [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia | cbn; lia ]).
apply HK.
- exact HJ.
- unfold spZ at 1; rewrite P2, Usp; rewrite unsigned_lit_small by lia; lia.
- rewrite P1; unfold SB_RET_RCF, AF_sup_broadcast; reflexivity.
- rewrite P8; exact (EE 10%nat 10%bv eq_refl).
- rewrite P9; exact ESP292.
- rewrite P10; exact ESP292.
- rewrite P11; reflexivity.
- rewrite P18; exact E32.
- intros r Hr Hr2 Hr8 Hr9 Hr18.
  assert (Hr' : r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by (unfold acallee_saved in Hr; lia).
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]];
  (etransitivity;
   [ first [exact P3 | exact P4 | exact P19 | exact P20 | exact P21 | exact P22 | exact P23 | exact P24
           | exact P25 | exact P26 | exact P27]
   | first [exact (EE 3%nat 3%bv eq_refl) | exact (EE 4%nat 4%bv eq_refl) | exact (EE 19%nat 19%bv eq_refl)
           | exact (EE 20%nat 20%bv eq_refl) | exact (EE 21%nat 21%bv eq_refl) | exact (EE 22%nat 22%bv eq_refl)
           | exact (EE 23%nat 23%bv eq_refl) | exact (EE 24%nat 24%bv eq_refl) | exact (EE 25%nat 25%bv eq_refl)
           | exact (EE 26%nat 26%bv eq_refl) | exact (EE 27%nat 27%bv eq_refl)] ]).
- exact Vra.
- exact Vs0.
- exact Vs1.
- exact Vs2.
- exact KEEP.
- exact VNC.
Qed.




(* the call of rec_calls_free(record.spill, 1) at 0x8afe8, then the store block from 0x8afec (sb_store) *)
Lemma sb8_call : forall ly S W regs mem md ch pl line R O Q regsP memP mdP,
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
0 <= pl < 2 ^ 64 ->
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) ->
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O ->
astr_atR (rdW W mem) pl line -> Z.of_nat (length line) + 1 <= LMAX + 1 ->
rec_repA B ly S (rdW W mem) R O ->
arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
length (r_calls R) = 16%nat ->
st_nev S + EV_SUP_BROADCAST R <= EV_MAX ->
blocks_bytes S + LIVE_SUP_BROADCAST line (snd (sup_broadcast_m R line)) <= LIVE_MAX ->
mo_ok MT S (XM_SUP_BROADCAST MT R line (snd (sup_broadcast_m R line))) ->
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly S W memP mdP 0 ->
spZ regsP = spZ regs - 32 ->
getr regsP 1 = Z_to_bv 64 (BASE + SB_RET_RCF) ->
getr regsP 8 = w64 pl -> getr regsP 9 = w64 A_REC_SPILL -> getr regsP 10 = w64 A_REC_SPILL -> getr regsP 11 = w64 1 ->
getr regsP 18 = Z_to_bv 64 SB_SB ->
(forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr regsP (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
aval_mem (rdW W memP) (spZ regs - 8) 8 (raZ regs) -> aval_mem (rdW W memP) (spZ regs - 16) 8 (s0Z regs) ->
aval_mem (rdW W memP) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
aval_mem (rdW W memP) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W memP a = rdW W mem a) ->
SRr SEGS W (mkCfg (mkst regsP (Z_to_bv 64 (SIGMA CS_rec_calls_free)) memP (seg_rom SEGS)) mdP)
(apost_baseF SEGS B SUP_BROADCAST_STK (sb_FP O) regs ly S W mem md (EV_SUP_BROADCAST R) (sb_post B MT ly S R line O)).
Proof.
intros ly S W regs mem md ch pl line R O Q regsP memP mdP HPRE HFRM Hfr8 HROD Hpl HBLK HAPL HSTR HLEN HREC HA HO HL16
Hev Hlive HMOK HJ Hsp R1 R8 R9 R10 R11 R18 RCS Vra Vs0 Vs1 Vs2 KEEP.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WSTK : SUP_BROADCAST_STK = 16592) by reflexivity.
assert (WRCF : REC_CALLS_FREE_STK = 16496) by reflexivity.
assert (Hlow : alloc_ceiling <= spZ regs - SUP_BROADCAST_STK) by (revert Hceil Hslo Hstk0; clear; intros; lia).
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr2. change (bv_modulus 64) with (2 ^ 64) in Hr2.
pose proof HJ as (HARP & _).
pose proof HA as (_ & _ & _ & HC & _).
pose proof HC as (_ & _ & _ & _ & HCsp & _).
destruct HCsp as (_ & Hn6 & HlP & _ & Hnav & HndP & HargP).
set (P := l_spill Q) in *.
assert (HPb : forall pn, In pn P -> In pn (ablocks B ly S)) by (intros pn H; exact (lay_blocks_in_bl _ _ _ _ _ _ _ HA (in_lay_spill Q pn H))).
assert (HPO : forall pn, In pn P -> In pn O) by (intros pn H; apply HO; exact (in_lay_spill Q pn H)).
destruct HBLK as (pb & kb & Hinb & Hpb1 & Hpb2).
destruct (al_blocks _ _ LAWS ly S W mem md pb kb HAR Hinb) as (_ & Hpb4 & Hpbc & _ & _ & _ & Hkb).
pose proof (req_size_pos kb ltac:(lia)) as [_ Hrqb].
(* the head wrote only its frame: the live blocks and the statics are kept *)
assert (KB : forall p k a, In (p, k) (ablocks B ly S) -> p <= a < p + req_size k -> rdW W memP a = rdW W mem a).
{ intros p k a Hin Ha. destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (_ & Hp4 & Hpc & _). apply KEEP; lia. }
assert (KS : forall a, inFP cmd_PG a -> rdW W memP a = rdW W mem a).
{ intros a Hpg. pose proof (Hsegs a (cif_prog_img a Hpg)). apply KEEP; lia. }
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW W memP)).
{ intros a H1 H2 H3.
  assert (Ha : 0 <= a < kLowMemEnd)
    by (destruct H1 as [(sg & Hsg & _ & Hr) | Hr];
        [exact (Hsegs a (ex_intro _ sg (conj Hsg Hr))) | exact (Hsegs a (cif_relro_img a Hr))]).
  rewrite KEEP by lia. exact (HROD a H1 H2 H3). }
assert (HAc : arep_at (ablocks B ly S) (rdW W memP) A_G_REC A_REC_SPILL R Q).
{ apply (arep_at_agree _ _ _ _ _ _ _ _ HA).
  - intros pn _ H; exact H.
  - intros j Hj. apply KS. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Hj; lia].
  - intros j Hj. apply KS. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Hj; lia].
  - intros pn Hpn j Hj. pose proof (lay_blocks_in_bl _ _ _ _ _ _ _ HA Hpn) as Hb.
    pose proof (req_size_pos (snd pn) ltac:(lia)) as [_ Hrq].
    apply (KB (fst pn) (snd pn)); [destruct pn; exact Hb | lia]. }
(* the events and the meter of the call *)
assert (HR16 : Nat.ltb (length (r_calls R)) 16 = false) by (rewrite HL16; reflexivity).
assert (EVQ : EV_REC_CALLS_FREE [P] = rec_spill_frees R).
{ unfold EV_REC_CALLS_FREE, rec_spill_frees. rewrite HR16. cbn [concat]. rewrite app_nil_r, HlP. reflexivity. }
assert (XMQ : XM_REC_CALLS_FREE MT [P] = rec_spill_frees R * mo_free MT) by (unfold XM_REC_CALLS_FREE; rewrite <- EVQ; reflexivity).
assert (HXR : 0 <= XM_ARG_LINE MT line) by (unfold XM_ARG_LINE, XM_REC_CANONICAL; apply (mo_malloc_nonneg MT MTL); lia).
assert (HXA : 0 <= XM_ANSWER MT (snd (sup_broadcast_m R line))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_broadcast_m R line))) + 1) ltac:(lia)). lia. }
(* the callee's footprint *)
pose proof (sb8_fp1 P) as HFP1.
assert (HSO1 : ~ YI16.sink_open_fp (rcf_fp A_REC_SPILL [P])).
{ intros H0. destruct (HFP1 0 H0) as [Hn | (b & m & Hin & Hr)]; [unfold A_REC_SPILL, CALL_OFF_NARGS in Hn; lia|].
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR (HPb _ Hin)) as (_ & Hb4 & _). lia. }
(* the spill's entry at the call *)
assert (HENT : forall i P', nth_error [P] i = Some P' -> (length P' <= 6)%nat /\
  aval_mem (rdW W memP) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P')) /\
  forall a pn, nth_error P' a = Some pn ->
    aval_mem (rdW W memP) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
    In pn (ablocks B ly S)).
{ intros i P' Hi. destruct i as [|i]; [|destruct i; discriminate Hi]. cbn in Hi. injection Hi as HPP. subst P'.
  replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0) with A_REC_SPILL by lia.
  split; [rewrite HlP; exact Hn6|]. split.
  - rewrite HlP. intros kk Hkk. rewrite KS; [exact (Hnav kk Hkk)|].
    exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; unfold CALL_OFF_NARGS; cbn in Hkk; lia].
  - intros a pn Ha.
    assert (Hlt : (a < length (snd (r_spill R)))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Ha; discriminate).
    destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
    destruct (HargP a s pn Es Ha) as (Hv & _ & Hin & _).
    split; [|exact Hin].
    intros kk Hkk. rewrite KS; [exact (Hv kk Hkk)|].
    exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]].
    unfold CALL_OFF_ARGS. cbn in Hkk. lia. }
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W regsP memP (Z_to_bv 64 (SIGMA CS_rec_calls_free))
    SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly S mdP 0
    REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [P]) (EV_REC_CALLS_FREE [P]) (-32) (Z_to_bv 64 (BASE + SB_RET_RCF)) [] _ HJ).
  - lia.
  - reflexivity.
  - lia.
  - rewrite WRCF. lia.
  - rewrite WRCF, WSTK. lia.
  - etransitivity; [exact (RCS 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) | exact Hgp].
  - etransitivity; [exact (RCS 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) | exact Htp].
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold SB_RET_RCF, AF_sup_broadcast; lia | reflexivity].
  - unfold SB_RET_RCF, AF_sup_broadcast. rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE2. rewrite sb8_sig_rcf.
    eapply SRr_mono.
    { apply (TREC_CALLS_FREE fx ly S W regsP memP mdP [] A_REC_SPILL [P] HPRE2).
      - exact HROD1.
      - exact R10.
      - exact R11.
      - cbn. lia.
      - right. left. change (Z.of_nat (length [P])) with 1. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE. lia.
      - unfold A_REC_SPILL. reflexivity.
      - exact HENT.
      - cbn [concat]. rewrite app_nil_r. exact HndP.
      - rewrite EVQ. unfold EV_SUP_BROADCAST, EV_ARG_LINE, EV_ANSWER, EV_REC_CANONICAL, EV_HAND_BACK, EV_XSTRDUP in Hev. lia.
      - apply (mo_ok_le MT MTL S _ _ HMOK). rewrite XMQ. unfold XM_SUP_BROADCAST. lia. }
    cbv beta. unfold apost_base. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2).
    exists ly2, S2, regs2, mem2, md2. split; [rewrite R1; reflexivity|]. split; [exact HJ2|]. split; [exact HP2 | exact HK2].
  - intros a Ha. destruct (HFP1 a Ha) as [Hn | (b & m & Hin & Hr)].
    + assert (Hpg : inFP cmd_PG a)
        by (exists (A_REC_SPILL, A_REC_SPILL + 56); split; [right; left; reflexivity | cbn [fst snd]; unfold CALL_OFF_NARGS in Hn; lia]).
      unfold awr_byte, awr_prog_or_caller. do 4 right. left.
      split; [exact (sb_slot_fp A_REC_SPILL a O (or_intror eq_refl) ltac:(unfold CALL_OFF_NARGS in Hn; lia))|].
      split; [exact (HPROG B HB a Hpg) | exact (cif_prog_img a Hpg)].
    + unfold awr_byte. right. left. split.
      * unfold sb_FP. do 4 (apply inFP_cons; right). replace a with (b + (a - b)) by lia.
        apply (inFP_ablocks_fp O b m (a - b)); [exact (HPO _ Hin) | lia].
      * exists b, m. split; [exact (HPb _ Hin) | exact Hr].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    destruct (HFP1 a Ha) as [Hn | (b & m & Hin & Hr)]; [unfold A_REC_SPILL, CALL_OFF_NARGS in Hn; lia|].
    destruct (al_blocks _ _ LAWS ly S W mem md b m HAR (HPb _ Hin)) as (_ & _ & Hc & _). lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & HK2).
destruct HK2 as (KP & _ & _ & KB2 & _ & KS2 & _ & _ & Kmle).
specialize (KS2 R Q HAc eq_refl eq_refl).
cbn [concat] in KP. rewrite app_nil_r in KP.
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & G1 & _ & G3 & _).
(* the frame survives the call: it lies above the callee's window and outside its footprint *)
assert (KF : forall a, spZ regs - 32 <= a < spZ regs -> rdW W2 mem2 a = rdW W memP a).
{ intros a Ha. apply G1; [lia | rewrite WRCF; lia |].
  intros Hf. destruct (HFP1 a Hf) as [Hn | (b & m & Hin & Hr)]; [unfold A_REC_SPILL, CALL_OFF_NARGS in Hn; lia|].
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR (HPb _ Hin)) as (_ & _ & Hc & _). lia. }
(* the line's block is none of the freed ones *)
assert (Hinb2 : In (pb, kb) (ablocks B ly2 S2)).
{ pose proof (Permutation_in _ KP Hinb) as Hx. apply in_app_or in Hx as [Hx | Hx]; [exact Hx|].
  exfalso. pose proof (proj1 (Forall_forall _ _) HAPL _ (HPO _ Hx)) as Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
set (Omid := concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) in *.
apply (sb_store B MT HB LAWS MTL VOBJS SIGP PRW cif_prog_img cif_prog_not_ro cif_relro_img cmd_ro_in_img cmd_ro_ok_of_aro
  TARG_LINE TANSWER ly S W regs mem md ch pl line R O ly2 S2 W2 regs2 mem2 md2 SB_RET_RCF A_REC_SPILL P Omid).
- left; reflexivity.
- exact HPRE.
- exact HFRM.
- exact Hfr8.
- exact HREC.
- exact Hev.
- exact Hlive.
- exact HMOK.
- rewrite <- EVQ. replace (EV_REC_CALLS_FREE [P]) with (0 + EV_REC_CALLS_FREE [P]) by lia. exact HJ2.
- assert (E2 : getr regs2 2 = getr regsP 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  unfold spZ in *. rewrite E2. exact Hsp.
- etransitivity; [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8].
- etransitivity; [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9].
- etransitivity; [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact R18].
- intros r Hr H2' H8' H9' H18'. rewrite (HP2 r Hr). exact (RCS r Hr H2' H8' H9' H18').
- intros kk Hkk. rewrite KF by (cbn in Hkk; lia). exact (Vra kk Hkk).
- intros kk Hkk. rewrite KF by (cbn in Hkk; lia). exact (Vs0 kk Hkk).
- intros kk Hkk. rewrite KF by (cbn in Hkk; lia). exact (Vs1 kk Hkk).
- intros kk Hkk. rewrite KF by (cbn in Hkk; lia). exact (Vs2 kk Hkk).
- intros a H1 H2 H3.
  assert (Himg : in_img SEGS a)
    by (destruct H1 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (cif_relro_img a Hr)]).
  rewrite (G3 a Himg H2 H3); [exact (HROD1 a H1 H2 H3)|].
  apply fp_spares_closed; [exact HSO1|].
  intros Hf. destruct (HFP1 a Hf) as [Hn | (b & m & Hin & Hr)].
  + exact (cif_prog_not_ro a (sb_slot_pg A_REC_SPILL a (or_intror eq_refl) ltac:(unfold CALL_OFF_NARGS in Hn; lia)) H1).
  + exact (blk_img SEGS B LAWS ly S W memP mdP b m a HARP (HPb _ Hin) Hr Himg).
- right; reflexivity.
- intros bl' rd' p k s HK1 HK2 HK3 Hfn Hna Harg Hin Hp4 Hk1 Hk2 Hstr Hap Hapg Haps.
  rewrite (rec_record_spill R _ _ HL16).
  change (set_spill R (REC_BROADCAST, [s])) with (set_spill (set_spill R (fst (r_spill R), [])) (REC_BROADCAST, [s])).
  apply (sb_rep_spill (ablocks B ly2 S2) (rdW W2 mem2) bl' rd' (set_spill R (fst (r_spill R), [])) Omid p k s KS2 eq_refl).
  + intros j Hj. apply HK1.
    * exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Hj; lia].
    * unfold A_G_REC, A_REC_SPILL, REC_SIZE in *. lia.
  + intros j Hj. apply HK1.
    * exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Hj; lia].
    * lia.
  + exact HK2.
  + intros pn Hpn _. exact (HK3 pn Hpn).
  + exact Hfn.
  + exact Hna.
  + exact Harg.
  + exact Hin.
  + exact Hp4.
  + exact Hk1.
  + exact Hk2.
  + exact Hstr.
  + exact Hap.
  + exact Hapg.
  + exact Haps.
- right. split; [reflexivity | rewrite (rec_record_spill R _ _ HL16); reflexivity].
- apply (astr_atR_agree (rdW W mem) (rdW W2 mem2) pl line (Z.of_nat (length line) + 1) HSTR ltac:(lia)).
  intros j Hj. replace (pl + j) with (pb + (pl - pb + j)) by lia.
  rewrite (KB2 pb kb (pl - pb + j) Hinb2 ltac:(lia)).
  apply (KB pb kb); [exact Hinb | lia].
- exact HLEN.
- exists pb, kb. split; [exact Hinb2 | lia].
- exact KP.
- exact HPO.
- intros pn Hpn. apply HO. unfold lay_blocks. subst Omid.
  apply in_app_or in Hpn as [H | H]; [apply in_or_app; left; exact H | apply in_or_app; right; apply in_or_app; right; exact H].
- intros pn Hpn. apply HO in Hpn. unfold lay_blocks in Hpn. subst Omid.
  apply in_app_or in Hpn as [H | H]; [left; apply in_or_app; left; exact H|].
  apply in_app_or in H as [H | H]; [right; exact H | left; apply in_or_app; right; exact H].
- intros pn Hpn. exact (proj2 (sb_rep_pos _ _ _ _ pn KS2 Hpn)).
- rewrite <- XMQ. exact Kmle.
Qed.


(* the spill arm (g_rec.ncalls = 16): the head to the call of rec_calls_free, the call, then the store block *)
Lemma sb_head_spill : forall ly S W regs mem md ch pl line R O,
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 pl -> 0 <= pl < 2 ^ 64 ->
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) ->
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O ->
astr_atR (rdW W mem) pl line -> Z.of_nat (length line) + 1 <= LMAX + 1 ->
rec_repA B ly S (rdW W mem) R O ->
length (r_calls R) = 16%nat ->
st_nev S + EV_SUP_BROADCAST R <= EV_MAX ->
blocks_bytes S + LIVE_SUP_BROADCAST line (snd (sup_broadcast_m R line)) <= LIVE_MAX ->
mo_ok MT S (XM_SUP_BROADCAST MT R line (snd (sup_broadcast_m R line))) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_broadcast) regs mem md)
(apost_baseF SEGS B SUP_BROADCAST_STK (sb_FP O) regs ly S W mem md (EV_SUP_BROADCAST R) (sb_post B MT ly S R line O)).
Proof.
intros ly S W regs mem md ch pl line R O HPRE HFRM Hfr8 HROD H10 Hpl HBLK HAPL HSTR HLEN HREC HL16 Hev Hlive HMOK.
pose proof HREC as (Q & HA & HO).
pose proof HA as (_ & _ & _ & (_ & _ & Hnc & _) & _).
assert (Hn16 : aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 16) by (rewrite HL16 in Hnc; exact Hnc).
apply (sb8_reach ly S W regs mem md ch O _ HPRE Hn16).
intros regsP memP mdP HJ Hsp R1 R8 R9 R10 R11 R18 RCS Vra Vs0 Vs1 Vs2 KEEP VNC.
apply (sb8_call ly S W regs mem md ch pl line R O Q regsP memP mdP HPRE HFRM Hfr8 HROD Hpl HBLK HAPL HSTR HLEN HREC HA HO
  HL16 Hev Hlive HMOK HJ Hsp R1).
- rewrite R8; exact H10.
- exact R9.
- exact R10.
- exact R11.
- exact R18.
- exact RCS.
- exact Vra.
- exact Vs0.
- exact Vs1.
- exact Vs2.
- intros a Ha Hna.
  destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS)) as [Hlo | Hlo]; [apply KEEP; [exact Ha | exact Hna | lia]|].
  destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS + 4)) as [Hhi | Hhi]; [|apply KEEP; [exact Ha | exact Hna | lia]].
  replace a with (A_G_REC + OFF_NCALLS + Z.of_nat (Z.to_nat (a - (A_G_REC + OFF_NCALLS)))) by lia.
  assert (Hk : (Z.to_nat (a - (A_G_REC + OFF_NCALLS)) < 4)%nat) by lia.
  rewrite (VNC _ Hk), (Hn16 _ Hk). reflexivity.
Qed.

End e. End f. End d.
