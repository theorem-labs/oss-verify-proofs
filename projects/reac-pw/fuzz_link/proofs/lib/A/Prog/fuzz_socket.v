(* fuzz_socket on image A (fuzz_link.asan 0x821cc, listing offset AF_fuzz_socket = 0; listing
   (internal path) (internal record, sha256 c29851f5d96a)): the walk of its contract
   lib/A/Prog/fuzz_socket_c.v `fuzz_socket_acontract` (link_amem.v `aleaf`, K = 32, EV 0, SIDE []).

   The walk runs the image's instructions symbolically at link's listing (LinkWalk.v / LinkWalkErrno.v run instances
   over the caller's journal ajournal_gx):
   - entry state ks_ss: the 32-byte frame (stack_region 32), the .got word of the shadow base and its cell
     (got_regionP, bcell_regionP 32: +0x2c..+0x34 load the shadow base into s2), and g_nl's six 32-bit fields
     socket_errno .. misuse (g + 0x4020c .. g + 0x40224, atoms 33..38, read and written at constant offsets);
   - the run stops at +0x28 `beqz s1` (socket_errno = 0?):
     * 0: +0x64..+0xb0 with the branch +0x68 `beqz a0` on open; open := 1, opened := opened + 1, misuse := 1 when open
       was set; a0 := 7; the run stops at the `ret`;
     * not 0: the call +0x38 of ___errno_location (aj_gx_errno_at, LinkWalkErrno.v), then a 4-byte region at
       a0 = tp - 164 = errno with its shadow entry, the instrumented check +0x3c..+0x48 (+0xb4..+0xbc), the store
       +0x4c to errno, socket_errno := 0, a0 := -1, `ret`. The run that stores errno is LinkWalkErrno.v's paj_run_xe
       (errno is not a byte the caller's journal lists; ERRF says the runtime does not own it).
   - each path ends at LinkWalk.v apost_leaf (the errno path at E \/ errno, then LinkWalkErrno.v apost_errno), with
     the Post from ks_post: the end memory's g_nl list (LinkWalkNlk.v anlk_after) and its six fields.

   Section hypotheses: LAWS, TL (PALib), LV (LinkVals) are the image instance's facts, as in pcap's walks (pcap
   PcapSourceClose.v Section e); ERRF (errno not in the runtime's owned static table) is discharged on the image by
   LinkWalkErrnoInst.v `link_errno_not_static`; ERRNO, ___errno_location's contract, by
   lib/A/Rt/RtErrnoLocClosed.v `link_errno_location_closed` (0x90a7c).

   Proves fuzz_socket (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtErrnoLoc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlk LinkWalkErrno LinkWalkErrnoInst fuzz_socket_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtErrnoLocClosed.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the entry state ---------------------------------------------------- *)
Definition ks_nl : YP09.region := YP09.mkRegion (Some (A_OBJ 2)) 0x4020c 0x40224 0x4020c 0x40224
  [YP09.mkChunk 0x4020c (CVal 4 (SOff 33 0)); YP09.mkChunk 0x40210 (CVal 4 (SOff 34 0));
   YP09.mkChunk 0x40214 (CVal 4 (SOff 35 0)); YP09.mkChunk 0x40218 (CVal 4 (SOff 36 0));
   YP09.mkChunk 0x4021c (CVal 4 (SOff 37 0)); YP09.mkChunk 0x40220 (CVal 4 (SOff 38 0))].
Definition ks_regions : smem := [stack_region 32; got_regionP; bcell_regionP 32; ks_nl].
Definition ks_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0);
           (33%nat, mkAF 0 (2 ^ 31 - 1) 0); (34%nat, mkAF 0 (2 ^ 31 - 1) 0); (35%nat, mkAF 0 1 0);
           (36%nat, mkAF 0 (2 ^ 31 - 2) 0); (37%nat, mkAF 0 (2 ^ 31 - 1) 0); (38%nat, mkAF 0 1 0);
           (A_OBJ 2, mkAF LA_G_NL LA_G_NL 0)] [] [].
Definition ks_ss : sstate := mkSS AF_fuzz_socket sr_atoms ks_regions None ks_facts.
Definition ks_extra (bs : list byte) : list word :=
  map (Z_to_bv 64) [SB; nk_socket_errno bs; nk_send_errno bs; nk_open bs; nk_opened bs; nk_closed bs; nk_misuse bs].
(* the errno region and its shadow entry, after the call (a0 is the call's havoc atom 40 + 4) *)
Definition ks_errno_region : YP09.region := YP09.mkRegion (Some 44%nat) 0 4 0 4 [].
Definition ks_SH : list shent := [mkSHE 44 0 4].

Lemma val_mem_some : forall segs m a (n : nat) v, val_mem segs m a n v ->
  forall j, a <= j < a + Z.of_nat n -> exists b, mbyte segs m j = Some b.
Proof.
  intros segs m a n v H j Hj.
  pose proof (H (Z.to_nat (j - a)) ltac:(lia)) as Hb.
  replace (a + Z.of_nat (Z.to_nat (j - a))) with j in Hb by lia.
  eexists; exact Hb.
Qed.

Ltac zrng := try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32);
  try change (Z.of_N 8) with 8; try change (Z.of_N 4) with 4; lia.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis ERRF : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Hypothesis ERRNO : aerrno_location_realizes SEGS B (pa_sigma LS____errno_location).

Lemma ks_vals : VAL (A_OBJ 1) = 0xa19d0 /\ VAL (A_OBJ 2) = LA_G_NL /\ VAL (A_OBJ 64) = 0xaa438 /\
  BASE = 0x821cc /\ pa_sigma LS____errno_location = 0x90a7c.
Proof.
  split; [rewrite (lv_obj LV 1) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 2) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 64) by (unfold link_nobj; lia); reflexivity|].
  split; [exact (lv_text LV) | rewrite (lv_sigma LV); reflexivity].
Qed.

Lemma st_ok_pi_region : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth (segs := SEGS) E (abs_ss VAL ss) ms i r HS Hi). Qed.

(* THE ENTRY STATE *)
Lemma ks_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) bs,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 32 -> spZ regs <= sp0 ->
  anlk_at SEGS (rdW W memc) LA_G_NL bs -> nlk_wf bs -> nk_opened bs + 1 < 2 ^ 31 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (ks_extra bs))) ks_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_fuzz_socket)) memc (seg_rom SEGS))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs HJ H16 Hwlo Hwhi HNK WF HON.
destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
destruct ks_vals as (V1 & V2 & V64 & VB & _).
rewrite V1, V64 in Kgot. rewrite V64 in Kcell.
pose proof WF as (Wnc & Wnx & Wns & Wni & Wop & Won & Wcl & Wmi & Wee & Wse & Wsd & _ & _).
pose proof HNK as [[Hab Hwr] HL].
assert (Hfld : forall off v, 0 <= off -> off + 4 <= NK_SIZE -> rdn bs off 4 = v ->
          val_mem SEGS (rdW W memc) (LA_G_NL + off) 4 v).
{ intros off v H0 H1 <-. exact (anlk_field SEGS (rdW W memc) LA_G_NL bs off 4 HNK H0 H1). }
set (E := Eimg (Ereg regs (ks_extra bs))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ks_extra bs)) n)
  by (intros n Hn; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (nk_socket_errno bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (nk_send_errno bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (nk_open bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (nk_opened bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (nk_closed bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (nk_misuse bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (Eg : ew E (A_OBJ 2) = Z_to_bv 64 LA_G_NL)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V2; reflexivity).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 0xa19d0)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V1; reflexivity).
assert (Ecell : ew E (A_OBJ 64) = Z_to_bv 64 0xaa438)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V64; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VBv : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
rewrite restrict_mkst_fx. unfold ks_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ks_regions, stack_region, got_regionP, bcell_regionP, ks_nl.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + fold E. rewrite (VBv _ _ Egot) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa19d0 0 8 (SOff (A_OBJ 64) 0) 0xaa438);
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VBv _ _ Ecell) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xaa438 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zrng | zrng |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + fold E. rewrite (VBv _ _ Eg) by (unfold LA_G_NL; lia).
    split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|].
    split; [intros o Ho; apply Hwr; rewrite HL; unfold NK_SIZE; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x4020c 4 (SOff 33 0) (nk_socket_errno bs));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40210 4 (SOff 34 0) (nk_send_errno bs));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40214 4 (SOff 35 0) (nk_open bs));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40218 4 (SOff 36 0) (nk_opened bs));
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x4021c 4 (SOff 37 0) (nk_closed bs));
        [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
    * apply (chunk_ok_val SEGS E _ LA_G_NL 0x40220 4 (SOff 38 0) (nk_misuse bs));
        [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zrng | zrng |].
      apply Hfld; [lia | unfold NK_SIZE; lia | reflexivity].
- apply pairwise_disjoint_of_extents.
  unfold ks_regions, stack_region, got_regionP, bcell_regionP, ks_nl, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite (VBv _ _ Egot), (VBv _ _ Ecell), (VBv _ _ Eg) by (unfold LA_G_NL; lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LA_G_NL.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [ks_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, E32, E33, E34, E35, E36, E37, E38, Eg.
  unfold nk_socket_errno, nk_send_errno, nk_open, nk_opened, nk_closed, nk_misuse in *.
  rewrite !unsigned_lit_small by (unfold SB, LA_G_NL; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, LA_G_NL.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* THE POST: the end memory's g_nl list and its six fields *)
Lemma ks_post : forall (m m' : word -> option byte) (regs regs2 : bvmap 5 word) bs se sd op on cl mi,
  anlk_at SEGS m LA_G_NL bs -> nlk_wf bs -> nk_opened bs + 1 < 2 ^ 31 ->
  (forall i, 0 <= i < NK_SIZE -> ~ (NK_SOCKET_ERRNO <= i < NK_MISUSE + 4) ->
     mbyte SEGS m' (LA_G_NL + i) = mbyte SEGS m (LA_G_NL + i)) ->
  (forall i, 0 <= i < NK_SIZE -> writable_at SEGS m' (LA_G_NL + i)) ->
  val_mem SEGS m' (LA_G_NL + NK_SOCKET_ERRNO) 4 se -> val_mem SEGS m' (LA_G_NL + NK_SEND_ERRNO) 4 sd ->
  val_mem SEGS m' (LA_G_NL + NK_OPEN) 4 op -> val_mem SEGS m' (LA_G_NL + NK_OPENED) 4 on ->
  val_mem SEGS m' (LA_G_NL + NK_CLOSED) 4 cl -> val_mem SEGS m' (LA_G_NL + NK_MISUSE) 4 mi ->
  sd = nk_send_errno bs -> cl = nk_closed bs ->
  (nk_socket_errno bs <> 0 ->
     getr regs2 10 = w64 (-1) /\ se = 0 /\ au32_at SEGS m' (as_errno B) (nk_socket_errno bs) /\
     op = nk_open bs /\ on = nk_opened bs /\ mi = nk_misuse bs) ->
  (nk_socket_errno bs = 0 ->
     getr regs2 10 = w64 NL_FD /\ se = 0 /\ op = 1 /\ on = nk_opened bs + 1 /\
     mi = (if nk_open bs =? 0 then nk_misuse bs else 1)) ->
  fuzz_socket_apost SEGS B regs m regs2 m'.
Proof.
intros m m' regs regs2 bs se sd op on cl mi HNK WF HON Hout Hwr Vse Vsd Vop Von Vcl Vmi Esd Ecl Herr Hok.
unfold fuzz_socket_apost. intros bs0 HNK0. rewrite (anlk_at_unique SEGS m LA_G_NL bs0 bs HNK0 HNK). clear bs0 HNK0.
pose proof WF as (Wnc & Wnx & Wns & Wni & Wop & Won & Wcl & Wmi & Wee & Wse & Wsd & Wcln & Wsln).
assert (Hrng : 0 <= se < 2 ^ 31 /\ 0 <= op <= 1 /\ 0 <= on < 2 ^ 31 /\ 0 <= mi <= 1).
{ destruct (Z.eq_dec (nk_socket_errno bs) 0) as [Z0|Z0].
  - destruct (Hok Z0) as (_ & -> & -> & -> & ->). destruct (nk_open bs =? 0); lia.
  - destruct (Herr Z0) as (_ & -> & _ & -> & -> & ->). lia. }
destruct Hrng as (Rse & Rop & Ron & Rmi).
destruct (anlk_after SEGS m m' LA_G_NL bs NK_SOCKET_ERRNO (NK_MISUSE + 4) HNK Hout) as (HNK' & Hrd_out & Hrd_val).
{ intros i Hi Hw. unfold NK_SOCKET_ERRNO, NK_MISUSE in Hw.
  destruct (Z_lt_le_dec i 0x40210); [apply (val_mem_some _ _ _ _ _ Vse); unfold NK_SOCKET_ERRNO; cbn; lia|].
  destruct (Z_lt_le_dec i 0x40214); [apply (val_mem_some _ _ _ _ _ Vsd); unfold NK_SEND_ERRNO; cbn; lia|].
  destruct (Z_lt_le_dec i 0x40218); [apply (val_mem_some _ _ _ _ _ Vop); unfold NK_OPEN; cbn; lia|].
  destruct (Z_lt_le_dec i 0x4021c); [apply (val_mem_some _ _ _ _ _ Von); unfold NK_OPENED; cbn; lia|].
  destruct (Z_lt_le_dec i 0x40220); [apply (val_mem_some _ _ _ _ _ Vcl); unfold NK_CLOSED; cbn; lia|].
  apply (val_mem_some _ _ _ _ _ Vmi); unfold NK_MISUSE; cbn; lia. }
{ exact Hwr. }
set (bs' := abytes_of SEGS m' LA_G_NL (Z.to_nat NK_SIZE)) in *.
assert (Fse : nk_socket_errno bs' = se) by (exact (Hrd_val NK_SOCKET_ERRNO 4%nat se ltac:(unfold NK_SOCKET_ERRNO; lia) ltac:(unfold NK_SOCKET_ERRNO, NK_SIZE; lia) ltac:(cbn; lia) Vse)).
assert (Fsd : nk_send_errno bs' = sd) by (exact (Hrd_val NK_SEND_ERRNO 4%nat sd ltac:(unfold NK_SEND_ERRNO; lia) ltac:(unfold NK_SEND_ERRNO, NK_SIZE; lia) ltac:(rewrite Esd; cbn; lia) Vsd)).
assert (Fop : nk_open bs' = op) by (exact (Hrd_val NK_OPEN 4%nat op ltac:(unfold NK_OPEN; lia) ltac:(unfold NK_OPEN, NK_SIZE; lia) ltac:(cbn; lia) Vop)).
assert (Fon : nk_opened bs' = on) by (exact (Hrd_val NK_OPENED 4%nat on ltac:(unfold NK_OPENED; lia) ltac:(unfold NK_OPENED, NK_SIZE; lia) ltac:(cbn; lia) Von)).
assert (Fcl : nk_closed bs' = cl) by (exact (Hrd_val NK_CLOSED 4%nat cl ltac:(unfold NK_CLOSED; lia) ltac:(unfold NK_CLOSED, NK_SIZE; lia) ltac:(rewrite Ecl; cbn; lia) Vcl)).
assert (Fmi : nk_misuse bs' = mi) by (exact (Hrd_val NK_MISUSE 4%nat mi ltac:(unfold NK_MISUSE; lia) ltac:(unfold NK_MISUSE, NK_SIZE; lia) ltac:(cbn; lia) Vmi)).
assert (Fout : forall off n, 0 <= off -> 0 <= n -> off + n <= NK_SOCKET_ERRNO -> rdn bs' off n = rdn bs off n)
  by (intros off n H0 H1 H2; apply Hrd_out; unfold NK_SOCKET_ERRNO, NK_SIZE in *; lia).
assert (Fout2 : forall off n, NK_MISUSE + 4 <= off -> 0 <= n -> off + n <= NK_SIZE -> rdn bs' off n = rdn bs off n)
  by (intros off n H0 H1 H2; apply Hrd_out; unfold NK_MISUSE, NK_SIZE in *; lia).
assert (Fee : nk_end_errno bs' = nk_end_errno bs)
  by (unfold nk_end_errno, fld_u32; apply Fout; unfold NK_END_ERRNO, NK_SOCKET_ERRNO; lia).
exists bs'. split; [exact HNK'|].
split.
{ apply (nlk_wf_same_queues bs bs' WF).
  - unfold nk_n_chunks, fld_u32. apply Fout; unfold NK_N_CHUNKS, NK_SOCKET_ERRNO; lia.
  - unfold nk_n_sent, fld_u32. apply Fout2; unfold NK_N_SENT, NK_MISUSE, NK_SIZE; lia.
  - unfold nk_n_if, fld_u32. apply Fout2; unfold NK_N_IF, NK_MISUSE, NK_SIZE; lia.
  - intros i Hi. unfold fld_u64. apply Fout; unfold NK_CHUNK_LEN, NK_SOCKET_ERRNO, NL_CHUNKS in *; lia.
  - intros i Hi. unfold fld_u64. apply Fout2; unfold NK_SENT_LEN, NK_MISUSE, NK_SIZE, NL_SENT_MAX in *; lia.
  - assert (Enx : nk_next bs' = nk_next bs)
      by (unfold nk_next, fld_u32; apply Fout; unfold NK_NEXT, NK_SOCKET_ERRNO; lia). lia.
  - lia.
  - lia.
  - rewrite Fcl, Ecl. lia.
  - lia.
  - lia.
  - lia.
  - rewrite Fsd, Esd. lia. }
split; [rewrite Fsd, Esd; reflexivity|]. split; [exact Fee|]. split; [rewrite Fcl, Ecl; reflexivity|].
split.
- intros Z0. destruct (Herr Z0) as (R10 & -> & Hau & -> & -> & ->).
  exact (conj R10 (conj Fse (conj Hau (conj Fop (conj Fon Fmi))))).
- intros Z0. destruct (Hok Z0) as (R10 & -> & -> & -> & ->).
  exact (conj R10 (conj Fse (conj Fop (conj Fon Fmi)))).
Qed.

(* the run's write permission: the frame, g_nl's six fields (the contract's write set), errno *)
Ltac ks_awr Hajw :=
  lazymatch goal with |- awr_ok_xe _ _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_xe_cons;
    [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ lia
      | lazymatch type of Ha with context [ew _ 2%nat] =>
          match goal with U : bv_unsigned (ew _ 2%nat) = _ |- _ => rewrite U in Ha end;
          left; left; split; [left; lia | lia] end
      | lazymatch type of Ha with context [ew _ 243%nat] =>
          match goal with U : bv_unsigned (ew _ 243%nat) = _ |- _ => rewrite U in Ha end;
          left; apply Hajw; exists (LA_G_NL + NK_SOCKET_ERRNO, LA_G_NL + NK_MISUSE + 4);
          split; [left; reflexivity | cbn [fst snd]; unfold NK_SOCKET_ERRNO, NK_MISUSE; lia] end
      | lazymatch type of Ha with context [ew _ 44%nat] =>
          match goal with U : bv_unsigned (ew _ 44%nat) = _ |- _ => rewrite U in Ha end;
          right; unfold aerrno; lia end ]
    | ]);
  apply awr_ok_xe_nil.

(* the bytes a walk of fuzz_socket may change: its frame, g_nl's six fields, errno *)
Definition ks_Zs (sp a : Z) : Prop :=
  (sp - 32 <= a < sp) \/ (LA_G_NL + 262668 <= a < LA_G_NL + 262692) \/ aerrno B a.

(* the bytes a run left as they were: every byte outside its write windows (YC4b.v kept_of_frame) *)
Ltac ks_kept HFr sp UN :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (ks_Zs sp) HFr
    ltac:(intros ?bb ?wlo ?whi ?aa ?Hin ?Hrr; vm_compute in Hin;
          repeat (destruct Hin as [?Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                   repeat match goal with U : bv_unsigned (ew _ ?n) = _ |- _ =>
                     lazymatch type of Hrr with context [ew _ n] => rewrite U in Hrr end end;
                   unfold ks_Zs, aerrno; lia |]);
          destruct Hin)) as UN.

(* chain a run's kept bytes and growth onto those since the call *)
Ltac ks_fold UN HGc UNk HG W memc sp :=
  lazymatch type of UNk with forall a, _ -> _ -> aview _ _ ?mN a = aview _ _ ?mO a =>
    let UN' := fresh "UN" in
    assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ ks_Zs sp a ->
              aview SEGS (w_H W) mN a = aview SEGS (w_H W) memc a)
      by (intros ?a ?Ha ?Hz; rewrite (UNk _ Ha Hz); exact (UN _ Ha Hz));
    clear UN UNk; rename UN' into UN end;
  lazymatch type of HG with mem_grows _ (mrestrict _ ?mN) =>
    let HG' := fresh "HGc" in
    assert (HG' : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mN))
      by (eapply mem_grows_trans; [exact HGc | exact HG]);
    clear HGc HG; rename HG' into HGc end.

(* a field the run left in a region at base atom n: its value at the end memory *)
Ltac ks_den :=
  cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
  repeat match goal with Eq : ew ?E0 ?n = Z_to_bv 64 _ |- context [ew ?E0 ?n] => rewrite Eq end;
  rewrite ?unsigned_lit_small by (unfold LA_G_NL in *; lia); rewrite ?Z.add_0_r; reflexivity.
Ltac ks_vfield HR U :=
  eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
  [ exact HR | exact U | repeat (first [left; reflexivity | right]) | ks_den | zrng | zrng ].

(* THE END of every path: the contract's apost from the end state of the walk *)
Lemma ks_finish : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs regs2 : bvmap 5 word)
    mem2 md2,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  sp0 - STK <= spZ regs - 32 -> spZ regs <= sp0 ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ks_Zs (spZ regs) a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  mem_grows (rdW W memc) (rdW W mem2) ->
  fuzz_socket_apost SEGS B regs (rdW W memc) regs2 (rdW W mem2) ->
  apost SK SEGS B 32 0 (fun a => inFP (fuzz_socket_awr regs (rdW W memc)) a) G XO OUT STK sp0 FP ly S W0 mem0 md0
    own lyc Sc W memc mdc k regs
    (fun ly2 S2 W2 regs2 mem2 md2 => S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       fuzz_socket_apost SEGS B regs (rdW W memc) regs2 (rdW W2 mem2))
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2
  HJ HJ2 Hlo Hhi Hfd Hfs HP UN HGr HPost.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
pose proof HJ2 as (_ & _ & (memS2 & HJ2i & _) & _).
pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof (pal_env B TL) as ENV. pose proof (proj1 ENV) as [Ee0 Ee1].
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
apply (apost_errno SK SEGS B LAWS ENV 32 0 _ G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ W _ HAR).
apply (apost_leaf SK SEGS B LAWS pa_segs_low 32 0 (fun a => inFP (fuzz_socket_awr regs (rdW W memc)) a \/ aerrno B a)
  G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 _ HJ HJ2);
  [lia | lia | lia | exact Hfd | exact Hfs | exact HP | | | | | ].
- intros a Ha Hw HE. apply UN; [exact Ha|]. unfold ks_Zs. intros [H|[H|H]].
  + exact (Hw H).
  + apply HE. left. exists (LA_G_NL + NK_SOCKET_ERRNO, LA_G_NL + NK_MISUSE + 4).
    split; [left; reflexivity | cbn [fst snd]; unfold NK_SOCKET_ERRNO, NK_MISUSE; lia].
  + apply HE. right. exact H.
- intros a Hp. exact (apresent_grows _ _ _ _ HGr Hp).
- intros a Ha. apply Hpres2. pose proof HJ2 as (_ & HXO2 & _). clear - Ha Hlo Hhi HXO2. lia.
- intros x [((lo, hi) & Hin & Hx) | Hx].
  + destruct Hin as [Hin|[]]. injection Hin as <- <-. cbn [fst snd] in Hx.
    unfold LA_G_NL, NK_MISUSE, SHADOW_OFF in *. lia.
  + unfold aerrno in Hx. unfold kLowMemEnd, SHADOW_OFF in *. lia.
- cbv beta. split; [destruct Sc; reflexivity|]. split; [apply Permutation_refl | exact HPost].
Qed.

Theorem fuzz_socket_aproof : forall rlo rhi, fuzz_socket_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi. unfold fuzz_socket_acontract, aleaf.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HP.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & _).
destruct HP as (bs & HNK & WF & HON & Herr & Hewr & Hesh & Hefr & Hegn).
unfold FUZZ_SOCKET_AK in *. unfold YK0s.ret_ok in Hret. unfold apart_frame, apart_gnl in Hefr, Hegn.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as HJ0.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct ks_vals as (V1 & V2 & V64 & VB & Vsig).
pose proof (pal_env B TL) as ENV. pose proof (proj1 ENV) as [Ee0 Ee1].
pose proof WF as (Wnc & Wnx & Wns & Wni & Wop & Won & Wcl & Wmi & Wee & Wse & Wsd & _ & _).
assert (HNKw : forall i, 0 <= i < NK_SIZE -> writable_at SEGS (rdW W memc) (LA_G_NL + i))
  by (destruct HNK as [[_ Hw] HL]; intros i Hi; apply Hw; rewrite HL; exact Hi).
pose proof (ks_entry G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bs HJ H16 Hwlo Hwhi HNK WF HON) as HS.
replace (cfg_at SEGS FUZZ_SOCKET_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_fuzz_socket)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, FUZZ_SOCKET_A, AF_fuzz_socket; rewrite VB; reflexivity).
remember (Eimg (Ereg regs (ks_extra bs))) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ks_extra bs)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (nk_socket_errno bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (nk_send_errno bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (nk_open bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (nk_opened bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (nk_closed bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (nk_misuse bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (Eg : ew E 243 = Z_to_bv 64 LA_G_NL)
  by (subst E; change 243%nat with (A_OBJ 2); rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (ks_extra bs)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Ug : bv_unsigned (ew E 243) = LA_G_NL) by (rewrite Eg; apply unsigned_lit_small; unfold LA_G_NL; lia).
clear HEdef EL.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) memc)) by constructor.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ks_Zs (spZ regs) a ->
          aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (HGc : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
pose proof (paj_run_xe SK B LAWS ENV ERRF G HGX XO OUT) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
(* g_nl's bytes outside the six fields, and its writability, at the end memory *)
assert (Hgout : forall (m2 : word -> option byte), (forall a, 0 <= a < 2 ^ 64 -> ~ ks_Zs (spZ regs) a ->
            aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a) ->
          forall i, 0 <= i < NK_SIZE -> ~ (NK_SOCKET_ERRNO <= i < NK_MISUSE + 4) ->
          mbyte SEGS (rdW W m2) (LA_G_NL + i) = mbyte SEGS (rdW W memc) (LA_G_NL + i)).
{ intros m2 U i Hi Hn. apply (mbyte_of_aview SEGS). apply U; [unfold LA_G_NL, NK_SIZE in *; lia|].
  unfold ks_Zs, aerrno, LA_G_NL, NK_SIZE, NK_SOCKET_ERRNO, NK_MISUSE in *. lia. }
assert (Hgwr : forall (m2 : word -> option byte), mem_grows (rdW W memc) (rdW W m2) ->
          forall i, 0 <= i < NK_SIZE -> writable_at SEGS (rdW W m2) (LA_G_NL + i)).
{ intros m2 Hg i Hi. apply (writable_kept (segs := SEGS) (w_H W) memc m2); [|exact (HNKw i Hi)].
  intros Hp. exact (apresent_grows _ _ _ _ Hg Hp). }
(* +0x00 .. +0x28: the frame, the shadow base, socket_errno, `beqz s1` *)
paj_run_tok RUN HS HJ SHOK Bspan; [ks_awr Hajw |].
ks_kept HFr (spZ regs) UNk. clear HF HFr. ks_fold UN HGc UNk HG W memc (spZ regs).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* socket_errno = 0: +0x64 `lw open`, +0x68 `beqz a0` *)
  rewrite branch_eq_U, (U_atom E 33 (nk_socket_errno bs) E33), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [ks_awr Hajw |].
  ks_kept HFr (spZ regs) UNk. clear HF HFr. ks_fold UN HGc UNk HG W memc (spZ regs).
  psrr_branch_tok RUN BR HS SHOK Bspan;
    rewrite branch_eq_U, (U_atom E 35 (nk_open bs) E35), U_lit in Hc0 by lia;
    [apply Z.eqb_eq in Hc0 | apply Z.eqb_neq in Hc0];
    (paj_run_tok RUN HS HJ SHOK Bspan; [ks_awr Hajw |]);
    ks_kept HFr (spZ regs) UNk; clear HF HFr; ks_fold UN HGc UNk HG W memc (spZ regs);
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
      pose proof (st_ok_pi_region _ _ _ 3 _ HS eq_refl) as HR;
      assert (Vse : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262668) 4 (nk_socket_errno bs)) by ks_vfield HR Ug;
      assert (Vsd : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262672) 4 (nk_send_errno bs)) by ks_vfield HR Ug;
      assert (Vop : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262676) 4 1) by ks_vfield HR Ug;
      assert (Von : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262680) 4 (nk_opened bs + 1)) by ks_vfield HR Ug;
      assert (Vcl : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262684) 4 (nk_closed bs)) by ks_vfield HR Ug;
      assert (Vmi : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262688) 4 (if nk_open bs =? 0 then nk_misuse bs else 1))
        by (destruct (Z.eqb_spec (nk_open bs) 0) as [?Ho|?Ho]; cbv beta iota;
            first [ks_vfield HR Ug | exfalso; lia]);
      prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
      pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regs (ks_extra bs) HS HAE ltac:(vm_compute; reflexivity)) as HP;
      eapply (paj_ret_at (PL := PL_link) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
      intros mat';
      rewrite R1, E1, Hret;
      apply (ks_finish G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msF) (ms_mem msF) _ HJ0);
      [ apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low); exact HJ
      | exact Hwlo | exact Hwhi
      | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact HP | exact UN | exact HGc
      | eapply (ks_post (rdW W memc) (rdW W (ms_mem msF)) regs (ms_regs msF) bs _ _ _ _ _ _ HNK WF HON
          (Hgout (ms_mem msF) UN) (Hgwr (ms_mem msF) HGc) Vse Vsd Vop Von Vcl Vmi eq_refl eq_refl);
        [ intros Hne; exfalso; exact (Hne Hc)
        | intros _; split; [exact R10|]; split; [exact Hc|]; split; [reflexivity|]; split; reflexivity ] ]
    end.
- (* socket_errno <> 0: the call of ___errno_location at +0x38 *)
  rewrite branch_eq_U, (U_atom E 33 (nk_socket_errno bs) E33), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [ks_awr Hajw |].
  ks_kept HFr (spZ regs) UNk. clear HF HFr. ks_fold UN HGc UNk HG W memc (spZ regs).
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into ms1 end.
  pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (4%bv : bv 5) R4.
  rewrite Usp in R2. rewrite E4 in R4.
  assert (Usp1 : spZ (ms_regs ms1) = spZ regs - 32)
    by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
  eapply SRr_bind.
  { eapply (aj_gx_errno_at SK SEGS B LAWS pa_segs_low (pa_sigma LS____errno_location) ERRNO G XO OUT W (ms_regs ms1)
      (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k _ HGX HJ);
      [rewrite Usp1; lia | rewrite Usp1; lia | exact R1 | apply ret_ok_codeptr_v; lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hsm & H10 & Hrk & Hm).
  assert (Emem : mem2 = ms_mem ms1) by (apply functional_extensionality; exact Hm). subst mem2. clear Hm.
  assert (HP2 : aregs_preserved (ms_regs ms1) regs2) by (intros r Hr; apply Hrk; unfold acallee_saved in Hr; lia).
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) (ms_mem ms1)) HP2 [0; 3]%nat HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
    (split; [intros; reflexivity | intros; assumption]). }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 40 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
  assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD : forall n, (n < 40)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite HE'; apply YN3v.ew_havoc_old; exact Hn).
  assert (HAE' : env_agree 32 (Ereg regs (ks_extra bs)) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
  assert (E1' : ew E' 1 = ew E 1) by (apply OLD; lia).
  assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
  assert (E32' : ew E' 32 = Z_to_bv 64 SB) by (rewrite OLD by lia; exact E32).
  assert (E33' : ew E' 33 = Z_to_bv 64 (nk_socket_errno bs)) by (rewrite OLD by lia; exact E33).
  assert (E34' : ew E' 34 = Z_to_bv 64 (nk_send_errno bs)) by (rewrite OLD by lia; exact E34).
  assert (E35' : ew E' 35 = Z_to_bv 64 (nk_open bs)) by (rewrite OLD by lia; exact E35).
  assert (E36' : ew E' 36 = Z_to_bv 64 (nk_opened bs)) by (rewrite OLD by lia; exact E36).
  assert (E37' : ew E' 37 = Z_to_bv 64 (nk_closed bs)) by (rewrite OLD by lia; exact E37).
  assert (E38' : ew E' 38 = Z_to_bv 64 (nk_misuse bs)) by (rewrite OLD by lia; exact E38).
  assert (Ug' : bv_unsigned (ew E' 243) = LA_G_NL) by (rewrite HE', ew_havoc_above by (cbn; lia); exact Ug).
  assert (E44 : ew E' 44 = Z_to_bv 64 (as_errno B)).
  { rewrite HE'. transitivity (getr regs2 10%bv); [reflexivity|].
    transitivity (w64 (bv_unsigned (getr (ms_regs ms1) 4) - 164)); [exact H10|].
    rewrite R4, Htp. unfold w64. rewrite unsigned_lit_small by lia. rewrite Herr. reflexivity. }
  assert (Uerr : bv_unsigned (ew E' 44) = as_errno B) by (rewrite E44; apply unsigned_lit_small; lia).
  clear HE' OLD.
  (* errno: a 4-byte region at a0 = tp - 164, its range fact and its shadow entry *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ss2 (restrict _ ?ms2) =>
    assert (HS3 : st_ok_pi SEGS VAL E' (add_atom (mkSS (ss_pc ss2) (ss_regs ss2) (ks_errno_region :: ss_mem ss2)
               (ss_resv ss2) (ss_facts ss2)) 44 (mkAF 0 (SB - 4) 0)) (restrict (w_H W) ms2))
  end.
  { apply st_ok_pi_add_fact.
    - apply st_ok_pi_add_region; [exact HS | vm_compute; reflexivity | |].
      + unfold region_ok, ks_errno_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Uerr. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. cbn [ms_mem restrict mkst].
        apply (writable_at_grows SEGS (rdW W memc)); [exact HGc | apply Hewr; lia].
      + apply all_disjoint_of_extents. unfold ks_errno_region, extent_of_region.
        cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Uerr, Usp', Ug'.
        cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LA_G_NL, NK_SIZE in *.
        repeat split; lia.
    - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Uerr. rewrite Z.pow_0_r, Z.mod_1_r.
      unfold SB, kLowMemEnd in *. lia. }
  clear HS. rename HS3 into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
  assert (SHOK3 : sh_ok SEGS (SOff 32 0) ks_SH E' (mrestrict (w_H W) (ms_mem ms1))).
  { unfold ks_SH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    rewrite (U_atom E' 32 SB E32') by (unfold SB; lia). rewrite (U_atom E' 44 (as_errno B) E44) by lia.
    rewrite ?Z.add_0_r, ?Z.sub_0_r. split.
    - rewrite <- (aview_rd_of SEGS). change SB with SHADOW_OFF.
      apply (ra_shadow_eq (ard SEGS (rdW W memc))); [exact Hesh|].
      intros x Hx. rewrite (ard_aview SEGS). unfold shadow_addr, SHADOW_OFF.
      apply UN; [unfold kLowMemEnd in *; pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia));
                 pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)); lia|].
      unfold ks_Zs, aerrno, LA_G_NL in *. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)). unfold kLowMemEnd in *. lia.
    - intros a Ha. unfold SB, kLowMemEnd in *. lia. }
  clear SHOK.
  (* +0x3c .. +0xb0: the instrumented check, errno := socket_errno, socket_errno := 0, a0 := -1, ret *)
  paj_run_tok RUN HS HJ2 SHOK3 Bspan; [ks_awr Hajw |].
  ks_kept HFr (spZ regs) UNk. clear HF HFr. ks_fold UN HGc UNk HG W memc (spZ regs).
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ (restrict _ ?msF) =>
    assert (HAEf : env_agree 32 (Ereg regs (ks_extra bs)) Ef)
      by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE' nn Hnn) | exact (proj2 HAE')]);
    pose proof (st_ok_pi_region _ _ _ 2 _ HS eq_refl) as HR;
    pose proof (st_ok_pi_region _ _ _ 0 _ HS eq_refl) as HRe;
    assert (Vse : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262668) 4 0) by ks_vfield HR Ug';
    assert (Vsd : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262672) 4 (nk_send_errno bs)) by ks_vfield HR Ug';
    assert (Vop : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262676) 4 (nk_open bs)) by ks_vfield HR Ug';
    assert (Von : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262680) 4 (nk_opened bs)) by ks_vfield HR Ug';
    assert (Vcl : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262684) 4 (nk_closed bs)) by ks_vfield HR Ug';
    assert (Vmi : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + 262688) 4 (nk_misuse bs)) by ks_vfield HR Ug';
    assert (Verr : val_mem SEGS (rdW W (ms_mem msF)) (as_errno B + 0) 4 (nk_socket_errno bs)) by ks_vfield HRe Uerr;
    rewrite Z.add_0_r in Verr;
    prreg HS (1%bv : bv 5) R1'; prreg HS (10%bv : bv 5) R10;
    pose proof (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs (ks_extra bs) HS HAEf ltac:(vm_compute; reflexivity)) as HP;
    eapply (paj_ret_at (PL := PL_link) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    intros mat';
    rewrite R1', E1', E1, Hret;
    apply (ks_finish G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msF) (ms_mem msF) _ HJ0);
    [ apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low); exact HJ2
    | exact Hwlo | exact Hwhi
    | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
      repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
    | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
      repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
    | exact HP | exact UN | exact HGc
    | eapply (ks_post (rdW W memc) (rdW W (ms_mem msF)) regs (ms_regs msF) bs _ _ _ _ _ _ HNK WF HON
        (Hgout (ms_mem msF) UN) (Hgwr (ms_mem msF) HGc) Vse Vsd Vop Von Vcl Vmi eq_refl eq_refl);
      [ intros _; split; [rewrite R10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|];
        split; [reflexivity|]; split; [exact Verr|]; split; [reflexivity|]; split; reflexivity
      | intros Hz; exfalso; exact (Hc Hz) ] ]
  end.
Qed.

End w.

(* The walk with LAWS, ERRNO and ERRF discharged on the image's segments: the allocator laws by lib/Reusable/YG0q.v
   `AR_laws_ok` (they hold at tfibsegs for every asyms), ___errno_location by
   lib/A/Rt/RtErrnoLocClosed.v `link_errno_location_closed` (0x90a7c), ERRF by LinkWalkErrnoInst.v
   `link_errno_not_static` from the image's asyms record (lib/A/AF0m.v PcapSyms; on the image lib/A/AD2l.v
   PcapB_syms). What stays is the image instance itself: its program tables (PI, whose segments are the image's),
   PALib and LinkVals. *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem fuzz_socket_aproof_img : forall B, PALib B -> LinkVals -> AF0m.PcapSyms B ->
  pa_segs = AB1v.tfibsegs -> forall rlo rhi, fuzz_socket_acontract SK pa_segs rlo rhi B.
Proof.
intros B TL LV TS Hsegs.
assert (LAWS : AR_laws pa_segs B) by (rewrite Hsegs; exact (YG0q.AR_laws_ok AB1v.tfibsegs B)).
apply (fuzz_socket_aproof SK B LAWS TL LV (link_errno_not_static B TS)).
rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. exact (RtErrnoLocClosed.link_errno_location_closed B).
Qed.
End img.

Print Assumptions fuzz_socket_aproof.
Print Assumptions fuzz_socket_aproof_img.

