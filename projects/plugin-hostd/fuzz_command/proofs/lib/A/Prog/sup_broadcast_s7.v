(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the table arm of plugin-hostd/fuzz_command's sup_broadcast walk (0x8afa0 ..
   0x8b008, g_rec.ncalls = n < 16): the head stores the frame, loads the shadow base and ncalls, takes the table
   branch, writes ncalls := n + 1 and s1 := the table's slot n, and falls into the store block at 0x8b00c
   (sup_broadcast_s5.v's sb_store). The slot's address depends on n, so the head's run is split into n's sixteen
   values (sb_tab_reach); one proof then applies sb_store.
   Pass-4/5 re-fit: the arm ends at apost_baseF and passes the rounding-mode-0 premise
   HFRM on to sb_store; statement pass 5 removed its astack_pres premise. *)
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
Let RUNTO := paj_run_to B LAWS.
Let STORE := sb_store B MT HB LAWS MTL VOBJS SIGP PRW cif_prog_img cif_prog_not_ro cif_relro_img cmd_ro_in_img
cmd_ro_ok_of_aro TARG_LINE TANSWER.

(* the run's static check (cells_safe_b) bounds every written window by the facts, and the window of g_rec's ncalls
   field is based on g_rec's atom: the walk adds g_rec's address as a fact to the entry state of sup_broadcast_s6.v *)
Lemma sb_st_ok_pi_add_atom : forall E ss ms m f,
st_ok_pi SEGS VAL E ss ms -> afact_ok E m f -> st_ok_pi SEGS VAL E (YP06.add_atom ss m f) ms.
Proof.
intros E [pc sr fr rs rv G] ms m f HS Hf.
unfold st_ok_pi, abs_ss, YP06.add_atom in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 _)))))))).
apply YP06.facts_ok_add_atom; assumption.
Qed.

(* the frame and the ncalls field after the head (0x8afa0 .. 0x8b008) *)
Definition sbh_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0
[YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
 YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition sbh_ncalls (n : Z) : YP09.region :=
YP09.mkRegion (Some SB_GREC) 8 12 8 12 [YP09.mkChunk 8 (CVal 4 (SLit (n + 1)))].

(* the head with the table arm, from the entry to the store block at 0x8b00c, for each of the sixteen values of
   ncalls; the facts at 0x8b00c go to the continuation HK *)
Lemma sb_tab_reach : forall ly S W regs mem md ch O (n : nat) (Q : world SEGS -> config -> Prop),
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat n) -> (n < 16)%nat ->
(forall regsP memP mdP,
 ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] ly S W memP mdP 0 ->
 spZ regsP = spZ regs - 32 ->
 getr regsP 8 = getr regs 10 ->
 getr regsP 9 = w64 (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n) ->
 getr regsP 18 = Z_to_bv 64 SB_SB ->
 (forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr regsP (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 aval_mem (rdW W memP) (spZ regs - 8) 8 (raZ regs) -> aval_mem (rdW W memP) (spZ regs - 16) 8 (s0Z regs) ->
 aval_mem (rdW W memP) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
 aval_mem (rdW W memP) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W memP a = rdW W mem a) ->
 aval_mem (rdW W memP) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat n + 1) ->
 SRr SEGS W (cfg_at SEGS (BASE + SB_STORE) regsP memP mdP) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_broadcast) regs mem md) Q.
Proof.
intros ly S W regs mem md ch O n Q HPRE Hn Hn16 HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WSTK : SUP_BROADCAST_STK = 16592) by reflexivity.
destruct (sbe_obj VOBJS) as (Vgrec & _ & _ & _).
destruct (sbe_entry B HB LAWS TL VOBJS PRW ly S W regs mem md ch (Z.of_nat n) HPRE Hn ltac:(lia)) as [HS0 SHOK].
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
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E (YP06.add_atom (ss_sbe (Z.of_nat n)) SB_GREC (mkAF A_G_REC A_G_REC 3))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_broadcast)) mem (seg_rom SEGS)))).
{ apply sb_st_ok_pi_add_atom; [exact HS0|]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ugrec.
  split; [lia|]. split; [reflexivity | lia]. }
clear HS0 HE.
unfold cfg_at. change (w64 (BASE + AF_sup_broadcast)) with (Z_to_bv 64 (BASE + AF_sup_broadcast)).
destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]].
17: lia.
all: (
paj_run_to_tok RUNTO HS HJ SHOK sbe_Bspan SB_STORE;
[ awr_ok_tac;
  first
  [ exact Usp
  | eapply (awr_ok_cons_gen B E _ _ _ _ _ _ _ _ _ _ 285%nat A_G_REC); [reflexivity | exact Ugrec285 | | apply awr_ok_nil];
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
    assert (Hpg : inFP cmd_PG a) by (exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; lia]);
    unfold awr_byte, awr_prog_or_caller; do 4 right; left;
    split; [unfold sb_FP; apply inFP_cons; left; unfold OFF_NCALLS; lia | split; [exact (HPROG B HB a Hpg) | exact (cif_prog_img a Hpg)]] ]
| pmkst HS;
  lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv := with_vm_backing x y z) in *; clearbody mdv end;
  prreg HS (2%bv : bv 5) P2; prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9; prreg HS (18%bv : bv 5) P18;
  prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
  prreg HS (19%bv : bv 5) P19; prreg HS (20%bv : bv 5) P20; prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22;
  prreg HS (23%bv : bv 5) P23; prreg HS (24%bv : bv 5) P24; prreg HS (25%bv : bv 5) P25; prreg HS (26%bv : bv 5) P26;
  prreg HS (27%bv : bv 5) P27;
  pose proof HS as HSo; unfold st_ok_pi in HSo;
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W (ms_mem ms) a = rdW W mem a) by
   (intros a Ha H1 H2; apply (kept_of_frame (segs:=SEGS) E _ (w_H W) mem (ms_mem ms)
      (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) HFr);
    [ intros b wlo whi a' Hin Hr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Ugrec285, ?Usp in Hr; cbv beta; unfold OFF_NCALLS; lia|]);
      destruct Hin
    | exact Ha | cbv beta; intros [Hc | Hc]; [exact (H1 Hc) | exact (H2 Hc)] ]);
  assert (Vs2 : aval_mem (rdW W (ms_mem ms)) (spZ regs - 32) 8 (bv_unsigned (getr regs 18))) by
   (apply sb_aval_of_val_mem;
    replace (spZ regs - 32) with (base_val E (YP09.r_base sbh_stack) + -32) by (cbn [YP09.r_base base_val sbh_stack]; rewrite Usp; lia);
    apply (sb_chunk_val (w_H W) E _ ms 0%nat sbh_stack 0%nat (-32) 8 (SOff 18 0) (bv_unsigned (getr regs 18)) HSo);
    [ vm_compute; reflexivity | vm_compute; reflexivity
    | cbn [sv_denot]; rewrite Z.add_0_r, (EE 18%nat 18%bv eq_refl); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr regs 18))
    | cbn; lia ]);
  assert (Vs1 : aval_mem (rdW W (ms_mem ms)) (spZ regs - 24) 8 (bv_unsigned (getr regs 9))) by
   (apply sb_aval_of_val_mem;
    replace (spZ regs - 24) with (base_val E (YP09.r_base sbh_stack) + -24) by (cbn [YP09.r_base base_val sbh_stack]; rewrite Usp; lia);
    apply (sb_chunk_val (w_H W) E _ ms 0%nat sbh_stack 1%nat (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) HSo);
    [ vm_compute; reflexivity | vm_compute; reflexivity
    | cbn [sv_denot]; rewrite Z.add_0_r, (EE 9%nat 9%bv eq_refl); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr regs 9))
    | cbn; lia ]);
  assert (Vs0 : aval_mem (rdW W (ms_mem ms)) (spZ regs - 16) 8 (s0Z regs)) by
   (apply sb_aval_of_val_mem;
    replace (spZ regs - 16) with (base_val E (YP09.r_base sbh_stack) + -16) by (cbn [YP09.r_base base_val sbh_stack]; rewrite Usp; lia);
    apply (sb_chunk_val (w_H W) E _ ms 0%nat sbh_stack 2%nat (-16) 8 (SOff 8 0) (s0Z regs) HSo);
    [ vm_compute; reflexivity | vm_compute; reflexivity
    | cbn [sv_denot]; rewrite Z.add_0_r, (EE 8%nat 8%bv eq_refl); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr regs 8))
    | cbn; lia ]);
  assert (Vra : aval_mem (rdW W (ms_mem ms)) (spZ regs - 8) 8 (raZ regs)) by
   (apply sb_aval_of_val_mem;
    replace (spZ regs - 8) with (base_val E (YP09.r_base sbh_stack) + -8) by (cbn [YP09.r_base base_val sbh_stack]; rewrite Usp; lia);
    apply (sb_chunk_val (w_H W) E _ ms 0%nat sbh_stack 3%nat (-8) 8 (SOff 1 0) (raZ regs) HSo);
    [ vm_compute; reflexivity | vm_compute; reflexivity
    | cbn [sv_denot]; rewrite Z.add_0_r, (EE 1%nat 1%bv eq_refl); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (bv_unsigned_in_range 64 (getr regs 1))
    | cbn; lia ]);
  lazymatch type of Hn16 with (?k < 16)%nat =>
  assert (VNC : aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat k + 1)) by
   (apply sb_aval_of_val_mem;
    replace (A_G_REC + OFF_NCALLS) with (base_val E (YP09.r_base (sbh_ncalls (Z.of_nat k))) + 8)
      by (cbn [YP09.r_base base_val sbh_ncalls]; rewrite Ugrec; reflexivity);
    apply (sb_chunk_val (w_H W) E _ ms 3%nat (sbh_ncalls (Z.of_nat k)) 0%nat 8 4 (SLit (Z.of_nat k + 1)) (Z.of_nat k + 1) HSo);
    [ vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia | cbn; lia ])
  end;
  apply HK;
  [ exact HJ
  | unfold spZ at 1; rewrite P2, Usp; rewrite unsigned_lit_small by lia; lia
  | rewrite P8; exact (EE 10%nat 10%bv eq_refl)
  | rewrite P9, Ugrec285; unfold w64; f_equal; unfold A_G_REC, OFF_CALLS, CALL_SIZE; reflexivity
  | rewrite P18; exact E32
  | intros r Hr Hr2 Hr8 Hr9 Hr18;
    assert (Hr' : r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by (unfold acallee_saved in Hr; lia);
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]];
    (etransitivity;
     [ first [exact P3 | exact P4 | exact P19 | exact P20 | exact P21 | exact P22 | exact P23 | exact P24
             | exact P25 | exact P26 | exact P27]
     | first [exact (EE 3%nat 3%bv eq_refl) | exact (EE 4%nat 4%bv eq_refl) | exact (EE 19%nat 19%bv eq_refl)
             | exact (EE 20%nat 20%bv eq_refl) | exact (EE 21%nat 21%bv eq_refl) | exact (EE 22%nat 22%bv eq_refl)
             | exact (EE 23%nat 23%bv eq_refl) | exact (EE 24%nat 24%bv eq_refl) | exact (EE 25%nat 25%bv eq_refl)
             | exact (EE 26%nat 26%bv eq_refl) | exact (EE 27%nat 27%bv eq_refl)] ])
  | exact Vra | exact Vs0 | exact Vs1 | exact Vs2 | exact KEEP | exact VNC ] ]).
Qed.

(* the table arm (g_rec.ncalls < 16): the head to 0x8b00c, then the store block *)
Lemma sb_head_table : forall ly S W regs mem md ch pl line R O,
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 pl -> 0 <= pl < 2 ^ 64 ->
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) ->
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O ->
astr_atR (rdW W mem) pl line -> Z.of_nat (length line) + 1 <= LMAX + 1 ->
rec_repA B ly S (rdW W mem) R O ->
(length (r_calls R) < 16)%nat ->
st_nev S + EV_SUP_BROADCAST R <= EV_MAX ->
blocks_bytes S + LIVE_SUP_BROADCAST line (snd (sup_broadcast_m R line)) <= LIVE_MAX ->
mo_ok MT S (XM_SUP_BROADCAST MT R line (snd (sup_broadcast_m R line))) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_broadcast) regs mem md)
(apost_baseF SEGS B SUP_BROADCAST_STK (sb_FP O) regs ly S W mem md (EV_SUP_BROADCAST R) (sb_post B MT ly S R line O)).
Proof.
intros ly S W regs mem md ch pl line R O HPRE HFRM Hfr8 HROD H10 Hpl HBLK HAPO HSTR HLEN HREC HHEAD Hev Hlive HMOK.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WSTK : SUP_BROADCAST_STK = 16592) by reflexivity.
pose proof HREC as (Q0 & HA & HO).
pose proof HA as (_ & _ & _ & (_ & _ & Hnc & _) & _).
assert (HSF : rec_spill_frees R = 0) by (unfold rec_spill_frees; rewrite (proj2 (Nat.ltb_lt _ _) HHEAD); reflexivity).
assert (HOX : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (proj2 (rec_repL_pos (ablocks B ly S) (rdW W mem) R O pn HREC Hpn))).
apply (sb_tab_reach ly S W regs mem md ch O (length (r_calls R)) _ HPRE Hnc HHEAD).
intros regsP memP mdP HJ Hsp H8 H9 H18 Hcs Vra Vs0 Vs1 Vs2 KEEP VNC.
(* every byte of a live block is kept *)
assert (KB : forall p k a, In (p, k) (ablocks B ly S) -> p <= a < p + req_size k -> rdW W memP a = rdW W mem a).
{ intros p k a Hin Ha. destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (_ & Hp4 & Hpc & _).
  apply KEEP; [lia | lia |]. intros Hn'. apply (blk_img SEGS B LAWS ly S W mem md p k a HAR Hin Ha).
  apply cif_prog_img. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS in Hn'; lia]. }
(* every static byte other than ncalls is kept *)
assert (KS : forall a, inFP cmd_PG a -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
  rdW W memP a = rdW W mem a).
{ intros a Hpg Hna. pose proof (Hsegs a (cif_prog_img a Hpg)). apply KEEP; [lia | lia | exact Hna]. }
apply (STORE ly S W regs mem md ch pl line R O ly S W regsP memP mdP SB_STORE
  (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) [] O).
- right; reflexivity.
- exact HPRE.
- exact HFRM.
- exact Hfr8.
- exact HREC.
- exact Hev.
- exact Hlive.
- exact HMOK.
- rewrite HSF; exact HJ.
- exact Hsp.
- rewrite H8; exact H10.
- exact H9.
- exact H18.
- exact Hcs.
- exact Vra.
- exact Vs0.
- exact Vs1.
- exact Vs2.
- intros a H1 H2 H3.
  assert (Ha : 0 <= a < kLowMemEnd)
    by (destruct H1 as [(sg & Hsg & _ & Hr) | Hr];
        [exact (Hsegs a (ex_intro _ sg (conj Hsg Hr))) | exact (Hsegs a (cif_relro_img a Hr))]).
  rewrite KEEP; [exact (HROD a H1 H2 H3) | lia | lia |].
  intros Hin. apply (cif_prog_not_ro a); [|exact H1].
  exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS in Hin; lia].
- left. exists (Z.of_nat (length (r_calls R))). split; [unfold REC_CALLS_MAX; lia | reflexivity].
- intros bl' rd' p k s HK1 HK2 HK3 Hfn Hna Harg Hin Hp4 Hk Hs Hstr Hap Hapg Haps.
  apply (sb_rep_slot (ablocks B ly S) (rdW W mem) bl' rd' R O (length (r_calls R)) p k s HREC eq_refl HHEAD).
  + intros j Hj Hnj Hsj.
    assert (Hpg : inFP cmd_PG (A_G_REC + j))
      by (exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Hj; lia]).
    rewrite HK1; [apply KS; [exact Hpg | lia] | exact Hpg |].
    clear - Hsj. unfold OFF_CALLS, CALL_SIZE in *. lia.
  + intros j Hj.
    assert (Hpg : inFP cmd_PG (A_REC_SPILL + j))
      by (exists (A_REC_SPILL, A_REC_SPILL + 56); split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Hj; lia]).
    rewrite HK1; [apply KS; [exact Hpg | unfold A_REC_SPILL, A_G_REC, OFF_NCALLS; lia] | exact Hpg |].
    clear - Hj HHEAD. unfold A_REC_SPILL, A_G_REC, OFF_CALLS, CALL_SIZE, SC_SIZE in *. lia.
  + intros pn Hpn j Hj. rewrite (HK2 pn Hpn j Hj).
    destruct (rec_repL_pos (ablocks B ly S) (rdW W mem) R O pn HREC Hpn) as [Hpos Hinb].
    pose proof (req_size_pos (snd pn) ltac:(lia)) as [_ Hrq].
    apply (KB (fst pn) (snd pn)); [destruct pn; exact Hinb | lia].
  + intros pn H1 _. exact (HK3 pn H1).
  + intros kk Hkk. cbn in Hkk.
    assert (Hpg : inFP cmd_PG (A_G_REC + OFF_NCALLS + Z.of_nat kk))
      by (exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS; lia]).
    rewrite HK1; [exact (VNC kk Hkk) | exact Hpg |].
    unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE. lia.
  + exact Hfn.
  + exact Hna.
  + exact Harg.
  + exact Hin.
  + exact Hp4.
  + exact Hk.
  + exact Hs.
  + exact Hstr.
  + exact Hap.
  + exact Hapg.
  + exact Haps.
- left. exists (length (r_calls R)). split; [|reflexivity].
  rewrite rec_record_calls by exact HHEAD. cbn [r_calls set_calls].
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
- destruct HBLK as (pb & kb & Hinb & Hpb1 & Hpb2).
  destruct (al_blocks _ _ LAWS ly S W mem md pb kb HAR Hinb) as (_ & _ & _ & _ & _ & _ & Hkb).
  pose proof (req_size_pos kb ltac:(lia)) as [_ Hrq].
  apply (astr_atR_agree (rdW W mem) (rdW W memP) pl line (Z.of_nat (length line) + 1) HSTR ltac:(lia)).
  intros kk Hkk. apply (KB pb kb); [exact Hinb | lia].
- exact HLEN.
- exact HBLK.
- rewrite app_nil_r. apply Permutation_refl.
- intros pn [].
- intros pn Hpn; exact Hpn.
- intros pn Hpn; left; exact Hpn.
- exact HOX.
- rewrite HSF, Z.mul_0_l. exact (mo_le_refl MT MTL S).
Qed.

End e. End f. End d.
