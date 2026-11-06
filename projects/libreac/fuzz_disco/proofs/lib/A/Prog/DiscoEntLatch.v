(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 365 of its 397 lines of code are new or changed and 37 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition lt_sr : list sv :=
  [SLit 0; SOff 536 0; SOff AT_A 0; SOff 3 0; SOff 4 0; SOff 537 0; SOff 538 0; SOff 539 0;
   SOff AT_STK 0; SOff AT_A 0; SOff 540 0; SOff 541 0; SOff 542 0; SOff 543 0; SOff 544 0; SOff 545 0;
   SOff 546 0; SOff 547 0; SOff 32 0; SOff 535 0; SLit WS_MASK; SOff 555 0; SOff 516 2992; SOff 548 0;
   SOff 549 0; SLit 32; SOff 516 2128; SOff 550 0; SOff 551 0; SOff 552 0; SOff 553 0; SOff 554 0].
Definition lt_acs0 : list YP09.chunk :=
  [YP09.mkChunk 224 (CVal 8 (SOff 531 0)); YP09.mkChunk 232 (CVal 8 (SOff 532 0));
   YP09.mkChunk 344 (CVal 8 (SOff 534 0))].
Definition lt_acs1 : list YP09.chunk := lt_acs0 ++ [YP09.mkChunk 248 (CVal 8 (SOff 533 0))].
Definition lt_rs (acs : list YP09.chunk) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ []);
   fshadow_region AT_SH DFRAME_CLASS 0 0 (dsh_chunks dsh_loop);
   got_regionP; bcell_regionP 32].

Lemma lt_sub : forall acs, submem (lt_rs acs) (d_kregions dsh_loop acs [] ++ []).
Proof.
intros acs. unfold lt_rs, d_kregions, fshadow_region. cbn [app].
repeat (apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
  split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|]).
apply submem_nil.
Qed.

Lemma lt_frame_eq : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hw x. apply HF. intros (r & Hr & Ha).
rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.

Lemma lt_mbyte_ext : forall segs (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof. intros segs H m m' HM a. unfold mbyte, mrestrict. rewrite HM. reflexivity. Qed.

Lemma lt_addw1 : forall E k i, ew E k = Z_to_bv 64 i -> 0 <= i < 2 ^ 31 - 1 ->
  sv_denot E (SAluw ALU_ADD (SOff k 0) (SLit 1)) = Z_to_bv 64 (i + 1).
Proof.
intros E k i Hk Hi. rewrite denot_lit_U. f_equal. rewrite U_of_S, S_SAluw.
rewrite (U_atom E k i Hk) by lia. rewrite U_lit by lia. cbn [zalu_raw].
rewrite (Z.mod_small i) by lia. rewrite (Z.mod_small 1) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small (i + 1 + 2 ^ 32 / 2)) by lia.
replace (i + 1 + 2 ^ 32 / 2 - 2 ^ 32 / 2) with (i + 1) by lia.
apply Z.mod_small. lia.
Qed.

Ltac lt_rg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Definition lt_vals (cx : dcx) (h i n now : Z) (regs : bvmap 5 word) : list word :=
  [w64 n; w64 i; w64 (d_cur cx n); w64 now; w64 h; getr regs 1; getr regs 5; getr regs 6; getr regs 7;
   getr regs 10; getr regs 11; getr regs 12; getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17;
   getr regs 23; getr regs 24; getr regs 27; getr regs 28; getr regs 29; getr regs 30; getr regs 31; getr regs 21].

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MT_TRIV : MT = ameter_triv.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.

Lemma lt_mono : forall cx pc kmax accmax
  (P P' : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop) W c,
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P W c ->
  (forall regs ly S W' mem md, P regs ly S W' mem md -> P' regs ly S W' mem md) ->
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P' W c.
Proof.
intros cx pc kmax accmax P P' W c (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hf0 & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HP) HPP.
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]). apply HPP. exact HP.
Qed.

Lemma lt_land : forall (fq : YK11.FPState) (cx : dcx) (h n : Z) ly3 S3 (W3 : world SEGS) mem3 md' k acc
  (E : env) (ss : sstate) (ms : machine_state) (pc kmax accmax : Z) (P : bvmap 5 word -> Prop),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax ->
  mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  d_E cx E -> ew E AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  d_land_chk dsh_loop (ss_mem ss) = true ->
  d_body B cx h n [] dsh_loop ly3 S3 W3 mem3 ->
  (forall x, ms_mem ms x = mem3 x) ->
  P (ms_regs ms) ->
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax
    (fun regs ly S W m md => P regs /\ d_body B cx h n [] dsh_loop ly S W m) W3 (mkCfg ms md').
Proof.
intros fq cx h n ly3 S3 W3 mem3 md' k acc E ss ms pc kmax accmax P
  HF0 HB HJ HFR Hk Hev Hmo Hacc HE HFL HS Hrv Hpc Hchk HBD MEQ HP.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 (ms_mem ms) md' k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 (ms_mem ms) md' k HC) as (_ & HSlo & HShi & _).
pose proof asan_consts as (C1 & _).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & _).
pose proof HBD as (T & G & Lk & H & HFRM & _ & _ & _ & HINP & _).
pose proof HFRM as (E0 & _ & _ & _ & V216 & V152).
pose proof HINP as (Rn & _).
pose proof (lt_mbyte_ext SEGS (w_H W3) mem3 (ms_mem ms) MEQ) as MB.
assert (V216' : val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 216) 8 h) by (intros j Hj; rewrite MB; exact (V216 j Hj)).
assert (V152' : val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 152) 8 (h + 440)) by (intros j Hj; rewrite MB; exact (V152 j Hj)).
destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_loop ly3 S3 W3 md' k E ss ms HC HE HFL HS Hchk V216' V152')
  as [HFRM' HSHD'].
assert (HBD' : d_body B cx h n [] dsh_loop ly3 S3 W3 (ms_mem ms)).
{ apply (d_body_keep B cx h n n dsh_loop ly3 S3 W3 mem3 (ms_mem ms) (d_A cx) (d_A cx) HBD).
  - unfold MFRAME, LLVMF_STK in *. lia.
  - unfold MFRAME, LLVMF_STK in *. lia.
  - intros a _ _. unfold aview. rewrite MB. reflexivity.
  - intros a _ (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite MEQ. exact Hb.
  - exact HFRM'.
  - exact HSHD'.
  - lia. }
pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HF0|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|]. split; [exact HP | exact HBD'].
Qed.

Lemma lt_exit_ok : forall (fq : YK11.FPState) (cx : dcx) (h n i : Z) ly3 S3 (W : world SEGS) mem3 md' k acc
  (E : env) (vals : list word) (ss : sstate) (ms : machine_state),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD (i + 1) -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD (i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT (i + 1) -> 0 <= i < MAX_OPS ->
  d_E cx E -> st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> ss_pc ss = EXIT_OFF -> d_land_chk dsh_loop (ss_mem ss) = true ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 -> (forall x, ms_mem ms x = mem3 x) ->
  d_rL B cx (ms_regs ms) -> getr (ms_regs ms) 19 = w64 h ->
  exit_pre B MT XM_LIB RLO RHI tfib_K cx h W (mkCfg ms md').
Proof.
intros fq cx h n i ly3 S3 W mem3 md' k acc E vals ss ms HF0 HB HJ HFR Hk Hev Hmo Hacc Ri HE HS Hrv Hpc Hchk HBD MEQ HL H19.
apply (lat_exit_weaken B MT XM_LIB RLO RHI tfib_K).
eapply lt_mono.
- apply (lt_land fq cx h n ly3 S3 W mem3 md' k acc (d_env cx E vals) ss ms EXIT_OFF (EV_HEAD MAX_OPS) (ACC_HEAD MT MAX_OPS)
    (fun r => d_rL B cx r /\ getr r 19 = w64 h) HF0 HB HJ HFR).
  + unfold EV_HEAD, EV_PRO, EV_ITER, MAX_OPS in *. lia.
  + unfold EV_HEAD, EV_PRO, EV_ITER, MAX_OPS in *. lia.
  + exact Hmo.
  + clear - Hacc Ri MT_TRIV. unfold ACC_HEAD, ACC_PRO, ACC_ITER, MAX_OPS in *. rewrite MT_TRIV in *.
    cbn [mo_malloc mo_free ameter_triv] in *. lia.
  + exact (d_E_env cx E vals HE).
  + exact (d_env_fl cx E vals).
  + exact HS.
  + exact Hrv.
  + exact Hpc.
  + exact Hchk.
  + exact HBD.
  + exact MEQ.
  + exact (conj HL H19).
- intros regs ly S W' m md [[HL' H19'] HBD']. exists n. split; [exact (d_rL_rX B cx h regs HL' H19') | exact HBD'].
Qed.

Lemma lt_hdr_ok : forall (fq : YK11.FPState) (cx : dcx) (h i n now : Z) ly3 S3 (W : world SEGS) mem3 md' k acc
  (E : env) (vals : list word) (ss : sstate) (ms : machine_state),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD (i + 1) -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD (i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT (i + 1) ->
  0 <= i + 1 < MAX_OPS -> 1 <= n -> 0 <= now < 2 ^ 64 ->
  d_E cx E -> st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> ss_pc ss = HDR_OFF -> d_land_chk dsh_loop (ss_mem ss) = true ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 -> (forall x, ms_mem ms x = mem3 x) ->
  d_rH B cx h (i + 1) n now (ms_regs ms) ->
  loop_inv B MT XM_LIB RLO RHI tfib_K cx h (i + 1) W (mkCfg ms md').
Proof.
intros fq cx h i n now ly3 S3 W mem3 md' k acc E vals ss ms HF0 HB HJ HFR Hk Hev Hmo Hacc Ri Rn Rnow HE HS Hrv Hpc Hchk HBD MEQ HP.
eapply lt_mono.
- exact (lt_land fq cx h n ly3 S3 W mem3 md' k acc (d_env cx E vals) ss ms HDR_OFF (EV_HEAD (i + 1)) (ACC_HEAD MT (i + 1))
    (d_rH B cx h (i + 1) n now) HF0 HB HJ HFR Hk Hev Hmo Hacc (d_E_env cx E vals HE) (d_env_fl cx E vals) HS Hrv Hpc Hchk HBD MEQ HP).
- intros regs ly S W' m md [HP' HBD']. exists n, now.
  split; [exact Ri|]. split; [exact Rn|]. split; [exact Rnow|]. split; [exact HP' | exact HBD'].
Qed.

Ltac lt_leaf_mem :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msf; cfg_model := _ |} _ =>
  lazymatch goal with HBD : d_body _ _ _ _ _ _ _ _ _ ?m0 |- _ =>
  let MEQ := fresh "MEQ" in
  assert (MEQ : forall x, ms_mem msf x = m0 x)
    by (intros x; repeat match goal with Mx : forall x, ms_mem _ x = _ |- _ => rewrite Mx; clear Mx end; reflexivity)
  end end.

Ltac lt_after_run :=
  lazymatch goal with HF : frame_of _ _ (ms_mem _) (ms_mem _) |- _ =>
    let M := fresh "M" in pose proof (lt_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as M;
    clear HF; repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.

Lemma lt_walk : forall (lat : bool) (cx : dcx) (h i n now : Z) (W : world SEGS) (fq : YK11.FPState)
  ly3 S3 (regs : bvmap 5 word) mem3 md3 k acc,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD (i + 1) -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD (i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT (i + 1) ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  d_rLAT B cx h regs ->
  (if lat then val_mem SEGS (rd W mem3) (d_A cx + 248) 8 (d_cur cx n) else getr regs 21 = w64 (d_cur cx n)) ->
  d_sp0 cx i now W mem3 -> val_mem SEGS (rd W mem3) (d_A cx + 224) 8 n ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + (if lat then LAT_OFF else L27_OFF)) regs mem3 md3)
    (fun W' c' => (i + 1 < MAX_OPS /\ 1 <= n /\ loop_inv B MT XM_LIB RLO RHI tfib_K cx h (i + 1) W' c') \/
                  exit_pre B MT XM_LIB RLO RHI tfib_K cx h W' c').
Proof.
intros lat cx h i n now W fq ly3 S3 regs mem3 md3 k acc HF0 HB HJ HFR Hk Hev Hmo Hacc Ri Rn Rnow HR HX HSP0 V224 HBD.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact HB | split; [exact HJ | exact HFR]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC) as (HSmod & HSlo & HShi & HFB1 & HFB2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
assert (RA : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof HBD as (T & G & Lk & H & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HSTK & HWR).
pose proof HFRM as (E & HE & HRG & HFL & V216 & V152).
pose proof HE as (EE & E32 & HEI & E60 & E516 & E529).
unfold AT_A, AT_F, AT_SH in E60, E516, E529.
pose proof HR as ((Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25) & H19 & H22 & H26).
pose proof HB as ((HPRE & HPX) & _).
pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp0 & Htp0 & Hstk & _).
pose proof HPX as (_ & _ & _ & HINdisj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HINP as (Rn' & _ & _).
assert (Rcn : c_n cx < 2 ^ 26) by (destruct HINdisj as [(-> & _) | (Hr & _)]; lia).
assert (Rcur : 0 <= d_cur cx n < 2 ^ 64).
{ unfold d_cur. destruct HINdisj as [(Hn0 & Hp0) | (Hnr & _)].
  - rewrite Hp0, Hn0. rewrite Hn0 in Rn'. unfold A_EMPTY. lia.
  - destruct HGEO as (_ & _ & _ & _ & _ & _ & _ & HGin). destruct (HGin (proj1 Hnr)) as (Hp0 & Hpc & _). lia. }
pose proof (d_E_env cx E (lt_vals cx h i n now regs) HE) as HEd.
pose proof HEd as (_ & _ & HEI' & _).
assert (AO : forall q, (q < AT_FL)%nat -> ew (d_env cx E (lt_vals cx h i n now regs)) q = ew E q)
  by (intros q Hq; apply d_env_old; exact Hq).
assert (AX : forall j, (j < 25)%nat ->
  ew (d_env cx E (lt_vals cx h i n now regs)) (AT_X + j) = nth j (lt_vals cx h i n now regs) (Z_to_bv 64 0))
  by (intros j Hj; apply d_env_x; cbn [length lt_vals]; lia).
assert (D60 : sv_denot (d_env cx E (lt_vals cx h i n now regs)) (SOff 60 0) = w64 (d_A cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E60).
assert (D2 : sv_denot (d_env cx E (lt_vals cx h i n now regs)) (SOff 2 0) = w64 (d_S cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D3 : sv_denot (d_env cx E (lt_vals cx h i n now regs)) (SOff 3 0) = w64 (as_gp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 3%nat 3%bv eq_refl); exact Hgp0).
assert (D4 : sv_denot (d_env cx E (lt_vals cx h i n now regs)) (SOff 4 0) = w64 (as_tp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 4%nat 4%bv eq_refl); exact Htp0).
assert (D32 : sv_denot (d_env cx E (lt_vals cx h i n now regs)) (SOff 32 0) = w64 SHADOW_OFF)
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E32).
assert (DX : forall j q, q = (AT_X + j)%nat -> (j < 25)%nat ->
  sv_denot (d_env cx E (lt_vals cx h i n now regs)) (SOff q 0) = nth j (lt_vals cx h i n now regs) (Z_to_bv 64 0))
  by (intros j q -> Hj; rewrite sv_denot_SOff0; exact (AX j Hj)).
assert (DF : forall c, 0 <= c < 4096 ->
  sv_denot (d_env cx E (lt_vals cx h i n now regs)) (SOff 516 c) = w64 (d_FB cx + c)).
{ intros c Hc. cbn [sv_denot]. rewrite AO by (unfold AT_FL; lia). rewrite E516. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (HROK : regs_ok (d_env cx E (lt_vals cx h i n now regs)) lt_sr regs).
{ apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
  repeat (destruct Hz as [<-|Hz];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
        let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
      lazymatch goal with
      | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
      | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H20 | exact H25 ]
      | |- _ = sv_denot _ (SOff 516 ?c) => rewrite (DF c) by lia;
          first [ exact H22 | exact H26 ]
      | |- _ = sv_denot _ (SOff 60 0) => rewrite D60;
          first [ exact H9 | unfold w64; rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned ]
      | |- _ = sv_denot _ (SOff 2 0) => rewrite D2; exact H8
      | |- _ = sv_denot _ (SOff 3 0) => rewrite D3; exact Hgp
      | |- _ = sv_denot _ (SOff 4 0) => rewrite D4; exact Htp
      | |- _ = sv_denot _ (SOff 32 0) => rewrite D32; exact H18
      | |- _ = sv_denot _ (SOff ?q 0) =>
          let j := eval vm_compute in (q - 531)%nat in
          rewrite (DX j q eq_refl ltac:(lia)); cbn [nth lt_vals]; first [ reflexivity | exact H19 ]
      end
    | ]).
  destruct Hz. }
assert (HFACTS : facts_ok (d_env cx E (lt_vals cx h i n now regs)) (d_facts [] []))
  by exact (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (lt_vals cx h i n now regs) [] [] HC HE I I).
assert (HACS0 : Forall (YP09.chunk_ok SEGS (d_env cx E (lt_vals cx h i n now regs)) (rd W mem3) (d_A cx)) lt_acs0).
{ destruct HSP0 as [V232 V344]. unfold lt_acs0.
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ n); [rewrite (DX 0%nat 531%nat eq_refl ltac:(lia)); reflexivity | cbn; lia | lia | exact V224].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ i); [rewrite (DX 1%nat 532%nat eq_refl ltac:(lia)); reflexivity | cbn; unfold MAX_OPS in Ri; lia | lia | exact V232].
  - apply (chunk_ok_val SEGS _ _ _ _ 8 _ now); [rewrite (DX 3%nat 534%nat eq_refl ltac:(lia)); reflexivity | cbn; lia | lia | exact V344]. }
assert (A531 : ew (d_env cx E (lt_vals cx h i n now regs)) 531%nat = Z_to_bv 64 n) by exact (AX 0%nat ltac:(lia)).
assert (A532 : ew (d_env cx E (lt_vals cx h i n now regs)) 532%nat = Z_to_bv 64 i) by exact (AX 1%nat ltac:(lia)).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_disco) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
destruct lat;
[ assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (lt_vals cx h i n now regs)) (rd W mem3) (d_A cx)) lt_acs1)
    by (unfold lt_acs1; apply Forall_app; split; [exact HACS0|]; apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val SEGS _ _ _ _ 8 _ (d_cur cx n));
        [rewrite (DX 2%nat 533%nat eq_refl ltac:(lia)); reflexivity | cbn; lia | lia | exact HX]);
  pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E LAT_OFF lt_sr
    (lt_vals cx h i n now regs) lt_acs1 [] [] (d_facts [] []) HC HE HRG HFL HROK HFACTS HACS (Forall_nil _) (Forall_nil _)
    I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0;
  pose proof (st_ok_pi_submem _ _ _ (lt_rs lt_acs1) HS0 (lt_sub lt_acs1) ltac:(vm_compute; reflexivity)) as HS1;
  clear HS0;
  unfold cfg_at; change (w64 (BASE + (if true then LAT_OFF else L27_OFF))) with (Z_to_bv 64 (BASE + LAT_OFF))
| pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E L27_OFF lt_sr
    (lt_vals cx h i n now regs) lt_acs0 [] [] (d_facts [] []) HC HE HRG HFL HROK HFACTS HACS0 (Forall_nil _) (Forall_nil _)
    I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0;
  pose proof (st_ok_pi_submem _ _ _ (lt_rs lt_acs0) HS0 (lt_sub lt_acs0) ltac:(vm_compute; reflexivity)) as HS1;
  clear HS0;
  unfold cfg_at; change (w64 (BASE + (if false then LAT_OFF else L27_OFF))) with (Z_to_bv 64 (BASE + L27_OFF)) ].
all: let lt_regL HS :=
  unfold d_rL;
  lt_rg HS (2%bv : bv 5) R2; lt_rg HS (3%bv : bv 5) R3; lt_rg HS (4%bv : bv 5) R4; lt_rg HS (8%bv : bv 5) R8;
  lt_rg HS (9%bv : bv 5) R9; lt_rg HS (18%bv : bv 5) R18; lt_rg HS (20%bv : bv 5) R20; lt_rg HS (25%bv : bv 5) R25;
  split; [unfold spZ; rewrite R2, D60; unfold w64; apply unsigned_lit_small; exact RA|];
  split; [rewrite R3; exact D3|]; split; [rewrite R4; exact D4|]; split; [rewrite R8; exact D2|];
  split; [rewrite R9; exact D60|]; split; [rewrite R18; exact D32|]; split; [rewrite R20; reflexivity|];
  rewrite R25; reflexivity in
let lt_exit HS :=
  lt_leaf_mem; apply SRr_ret; right;
  lazymatch goal with MEQ : forall x, ms_mem _ x = _ |- _ =>
  eapply (lt_exit_ok fq cx h n i ly3 S3 W mem3 _ k acc E (lt_vals cx h i n now regs) _ _ HF0 HB HJ HFR Hk Hev Hmo Hacc Ri HE HS
    eq_refl eq_refl ltac:(vm_compute; reflexivity) HBD MEQ);
  [ lt_regL HS | lt_rg HS (19%bv : bv 5) R19; rewrite R19, (DX 4%nat 535%nat eq_refl ltac:(lia)); reflexivity ] end in
let lt_hdr HS :=
  lt_leaf_mem; apply SRr_ret; left;
  rewrite branch_ltu_U, U_lit, (U_atom _ 532%nat i A532) in Hc1 by (unfold MAX_OPS in Ri; lia);
  apply Z.ltb_ge in Hc1;
  rewrite branch_eq_U, (U_atom _ 531%nat n A531), U_lit in Hc2 by lia;
  apply Z.eqb_neq in Hc2;
  split; [unfold MAX_OPS in *; lia|]; split; [lia|];
  lazymatch goal with MEQ : forall x, ms_mem _ x = _ |- _ =>
  apply (lt_hdr_ok fq cx h i n now ly3 S3 W mem3 _ k acc E (lt_vals cx h i n now regs) _ _ HF0 HB HJ HFR Hk Hev Hmo Hacc
    ltac:(unfold MAX_OPS in *; lia) ltac:(lia) Rnow HE HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HBD MEQ) end;
  unfold d_rH; split; [lt_regL HS|];
  lt_rg HS (19%bv : bv 5) R19; lt_rg HS (6%bv : bv 5) R6; lt_rg HS (7%bv : bv 5) R7; lt_rg HS (11%bv : bv 5) R11;
  lt_rg HS (14%bv : bv 5) R14; lt_rg HS (21%bv : bv 5) R21; lt_rg HS (22%bv : bv 5) R22; lt_rg HS (26%bv : bv 5) R26;
  split; [rewrite R19, (DX 4%nat 535%nat eq_refl ltac:(lia)); reflexivity|];
  split; [rewrite R6, (lt_addw1 _ 532%nat i A532) by (unfold MAX_OPS in *; lia); reflexivity|];
  split; [rewrite R7, (DX 0%nat 531%nat eq_refl ltac:(lia)); reflexivity|];
  split; [rewrite R11, (DX 3%nat 534%nat eq_refl ltac:(lia)); reflexivity|];
  split; [rewrite R14, (DF 2160) by lia; reflexivity|];
  split; [rewrite R21; first [ rewrite (DX 2%nat 533%nat eq_refl ltac:(lia)); reflexivity
                             | rewrite (DX 24%nat 555%nat eq_refl ltac:(lia)); exact HX ]|];
  split; [rewrite R22, (DF 2992) by lia; reflexivity | rewrite R26, (DF 2128) by lia; reflexivity] in
  paj_run_to_sh RUNTO HS1 HJ HDR_OFF; [awr_ok_tac | lt_after_run;
  apply (BR W _ _ _ _ _ BC_LTU (SLit 510) (SOff 532 0) HS1); intros Hc1 HS2;
  [ paj_run_to_sh RUNTO HS2 HJ EXIT_OFF; [awr_ok_tac | lt_after_run; lt_exit HS2]
  | paj_run_to_sh RUNTO HS2 HJ HDR_OFF; [awr_ok_tac | lt_after_run;
    apply (BR W _ _ _ _ _ BC_EQ (SOff 531 0) (SLit 0) HS2); intros Hc2 HS3;
    [ paj_run_to_sh RUNTO HS3 HJ EXIT_OFF; [awr_ok_tac | lt_after_run; lt_exit HS3]
    | paj_run_to_sh RUNTO HS3 HJ HDR_OFF; [awr_ok_tac | lt_after_run; lt_hdr HS3] ] ] ] ].
Qed.

Theorem pb_latch : latch_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold latch_spec. intros cx h i n now W c [Hpre | Hpre].
- destruct Hpre as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
    Ri & Rn & Rnow & HR & (HSP0 & V224 & V248) & HBD).
  exact (lt_walk true cx h i n now W fq ly3 S3 regs mem3 md3 k acc HF0 HB HJ HFR Hk Hev Hmo Hacc Ri Rn Rnow HR V248 HSP0 V224 HBD).
- destruct Hpre as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
    Ri & Rn & Rnow & HR & H21 & HSP0 & V224 & HBD).
  exact (lt_walk false cx h i n now W fq ly3 S3 regs mem3 md3 k acc HF0 HB HJ HFR Hk Hev Hmo Hacc Ri Rn Rnow HR H21 HSP0 V224 HBD).
Qed.
End h.
End f.
End d.
