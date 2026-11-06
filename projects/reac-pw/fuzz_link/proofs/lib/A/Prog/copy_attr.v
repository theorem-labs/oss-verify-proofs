(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 327 of its 364 lines of code are new or changed and 1268 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readDefs.v, with its module names changed; 1004 of its 1049 lines of code are new or changed and 319 lines of the source are left out. *)
(* copy_attr (reac_link_alias.c:25-35) on image A (fuzz_link.asan 0x89438, 204 bytes, 51 instructions; listing
   (internal path) (internal record, sha256 cabe69abda9c)): the walk of lib/A/Prog/copy_attr_c.v
   `copy_attr_acontract` on link's program tables, through the walk kit lib/A/Prog/LinkWalk.v and LinkWalkLeaf.v.

   The walk, in the symbolic runner of the caller's journal ajournal_gx (atoms: 2 = sp, 10 = a, 11 = out, 12 = n,
   32 = the shadow base, 33 = l, 34 = q = out + s3 with s3 = min (nul_at pay) (n - 1)):
   - +0x00 .. +0x24: the 48-byte frame and the saves, `beqz a1`, `beqz a2`. The entry state holds the frame, the
     .got slot 0xa19d0 (A_OBJ 1) and the shadow-base cell 0xaa438 (A_OBJ 64), whose words AR's const law gives.
     out = 0 and n = 0 run the epilogue to the `ret` (paths A and B): the Post's conjuncts are under out <> 0 and
     n >= 1, and the write set is empty.
   - +0x2c .. +0x44: the shadow base into s4 and the instrumented check of the 2-byte load of a->rta_len, on the
     shadow entry [a, a + 2) of the Pre's range_addressable (the error path errpath_load2 is not reached). The run
     stops at +0x48; the two .got regions are dropped (st_ok_pi_keep: the attribute may lie anywhere in the image)
     and the region of the length field (a chunk over atom 33) is added.
   - +0x48 .. +0x58: `lhu`, then wrapper_strnlen(a + 4, l - 4) through LinkWalkStrS.v aj_gx_strnlen_atS (link_ajkit.v
     aj_gx_strnlen_at keeping the model relation) over the Section hypothesis ASTRNLEN; its answer is nul_at pay
     (ca_first_nul).
   - +0x5c .. +0x74: the `bltu` cap s3 = min (nul_at pay) (n - 1), then checked_memcpy(out, a + 4, s3) through
     aj_gx_intrin_at over AMEMCPY.
   - +0x78 .. +0xac: an alias names out + s3 as atom 34, so the instrumented check of the 1-byte store (shadow entry
     [q, q + 1), errpath_store1 not reached) and `sb zero, 0(out + s3)` run on the region of q; then the epilogue
     and the `ret`. The Post follows from the bytes the copy wrote and the NUL (ca_post_c, ca_abuf_kept), and the
     whole apost from LinkWalkLeaf.v apost_leaf_app (the write set [out, out + n) lies outside the shadow band).

   Section hypotheses: the image instance (PI : PAImg link_listing), its symbol table (HV : LinkVals) and the .got
   record (TL : PALib B), the allocator laws (LAWS : AR_laws pa_segs B), the two runtime contracts
   (ASTRNLEN : astrnlen_whole_realizesM pa_segs B 0x10360 0x10380 0x43048, discharged at the instance by
   lib/A/Rt/RtClosed.v link_strnlenM_closed; AMEMCPY : aintrin_realizes pa_segs B OCpy 0x52d78, discharged by
   lib/A/AE2q.v asan_memcpy_realizes), the segments (HSEGS : pa_segs = tfibsegs, by reflexivity at the link
   instance) and the symbol record (TB : PcapSyms B, instance lib/A/AD2l.v PcapB_syms). The last two give, by
   computation (ca_roc), that the 32 bytes 0x10360 .. 0x1037f are read-only image bytes outside the runtime's
   statics and errno, from which the Pre's arodata_okP gives the strnlen contract's consts_view.

   Released proofs (rule 24): none; the rule-24 walk check confirmed it, disposition none: written new.
   Proves function copy_attr (image A, the asan build). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import ConstsViewDef StrnlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b YC85G.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkLeaf LinkWalkStrS copy_attr_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   The byte algebra of the walk (no image)
   ========================================================================== *)
Section p.
Variable segs : list Segment.

(* The answer of the strnlen wrapper over the payload is nul_at of the payload: first_byte's three facts, read
   against the payload's bytes, fix it. *)
Lemma ca_first_nul : forall (pay : list byte) (rd : Z -> option Z) x j,
  (forall i, 0 <= i < Z.of_nat (length pay) ->
     rd (x + i) = option_map (fun b : byte => bv_unsigned b) (nth_error pay (Z.to_nat i))) ->
  0 <= j <= Z.of_nat (length pay) ->
  (forall i, 0 <= i < j -> exists b, rd (x + i) = Some b /\ b <> 0) ->
  (j < Z.of_nat (length pay) -> rd (x + j) = Some 0) ->
  j = Z.of_nat (nul_at pay).
Proof.
  induction pay as [|b pay IH]; intros rd x j Hrd Hj Hlt Hat.
  - cbn [length Z.of_nat] in Hj. cbn [nul_at]. lia.
  - cbn [length nul_at] in *.
    assert (Hx : rd x = Some (bv_unsigned b)).
    { pose proof (Hrd 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0. reflexivity. }
    unfold bz. destruct (Z.eqb_spec (bv_unsigned b) 0) as [Hb0 | Hb0].
    + destruct (Z_le_gt_dec j 0) as [Hj0|Hj0]; [lia|].
      destruct (Hlt 0 ltac:(lia)) as (v & Hv & Hv0). rewrite Z.add_0_r, Hx in Hv. injection Hv as <-. lia.
    + destruct (Z_le_gt_dec j 0) as [Hj0|Hj0].
      * exfalso. assert (Ej : j = 0) by lia. subst j.
        pose proof (Hat ltac:(lia)) as H0. rewrite Z.add_0_r, Hx in H0. injection H0 as H0. lia.
      * enough (Hrec : j - 1 = Z.of_nat (nul_at pay)) by lia.
        apply (IH rd (x + 1) (j - 1)).
        -- intros i Hi. replace (x + 1 + i) with (x + (i + 1)) by lia. rewrite (Hrd (i + 1) ltac:(lia)).
           replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
        -- lia.
        -- intros i Hi. replace (x + 1 + i) with (x + (i + 1)) by lia. apply Hlt. lia.
        -- intros Hj1. replace (x + 1 + (j - 1)) with (x + j) by lia. apply Hat. lia.
Qed.

(* the 16-bit length the Pre names is the one the Post names *)
Lemma ca_u16_same : forall (m : word -> option byte) a l l',
  val_mem segs m a 2 l -> val_mem segs m a 2 l' -> 0 <= l < 65536 -> 0 <= l' < 65536 -> l = l'.
Proof.
  intros m a l l' H H' R R'.
  destruct (mbyte segs m (a + Z.of_nat 0)) as [b0|] eqn:E0; [|pose proof (H 0%nat ltac:(lia)); congruence].
  destruct (mbyte segs m (a + Z.of_nat 1)) as [b1|] eqn:E1; [|pose proof (H 1%nat ltac:(lia)); congruence].
  assert (X : forall v, val_mem segs m a 2 v -> 0 <= v < 65536 -> bytes_le_to_Z [b0; b1] = v).
  { intros v Hv Rv. apply (lw_bytes_of_vals 2 [b0; b1] v eq_refl ltac:(cbn; lia)).
    intros kk Hkk. destruct kk as [|[|kk]]; [| |lia]; cbn [nth_error].
    - rewrite <- E0. exact (Hv 0%nat ltac:(lia)).
    - rewrite <- E1. exact (Hv 1%nat ltac:(lia)). }
  rewrite <- (X l H R), <- (X l' H' R'). reflexivity.
Qed.

(* the payload the Pre names is the one the Post names *)
Lemma ca_abytes_same : forall (m : word -> option byte) a (bs bs' : list byte),
  abytes segs m a bs -> abytes segs m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
  intros m a bs bs' (_ & _ & H) (_ & _ & H') HL. apply lw_list_ext; [exact HL|].
  intros kk Hk. rewrite <- (H kk Hk), <- (H' kk ltac:(lia)). reflexivity.
Qed.

(* THE C STRING the code leaves at out: the s3 bytes the copy wrote and the NUL after them. *)
Lemma ca_post_c : forall (m m2 : word -> option byte) (a out n l : Z) (pay : list byte),
  au16_at segs m a l -> RTA_HDR <= l <= 65535 -> abytes segs m (a + RTA_HDR) pay ->
  Z.of_nat (length pay) = l - RTA_HDR -> 1 <= n -> 0 <= out -> out + n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.min (Z.of_nat (nul_at pay)) (n - 1) ->
     mbyte segs m2 (out + i) = mbyte segs m (a + RTA_HDR + i)) ->
  mbyte segs m2 (out + Z.min (Z.of_nat (nul_at pay)) (n - 1)) = Some (zb 0) ->
  forall l' pay', au16_at segs m a l' -> RTA_HDR <= l' <= 65535 -> abytes segs m (a + RTA_HDR) pay' ->
    Z.of_nat (length pay') = l' - RTA_HDR -> acstr_at segs m2 out (cut_text pay' n).
Proof.
  intros m m2 a out n l pay HU Hl HB Hlen Hn Hout Hon HC HZ l' pay' HU' Hl' HB' Hlen'.
  assert (El : l' = l) by (eapply ca_u16_same; [exact HU' | exact HU | unfold RTA_HDR in *; lia | unfold RTA_HDR in *; lia]).
  subst l'.
  assert (Ep : pay' = pay) by (eapply ca_abytes_same; [exact HB' | exact HB | lia]). subst pay'.
  pose proof (nul_at_le pay) as NL.
  assert (CT : cut_text pay n = firstn (Z.to_nat (Z.min (Z.of_nat (nul_at pay)) (n - 1))) pay) by reflexivity.
  set (s := Z.min (Z.of_nat (nul_at pay)) (n - 1)) in *.
  assert (Hs : 0 <= s <= n - 1) by (subst s; lia).
  assert (Hsl : s <= Z.of_nat (length pay)) by (subst s; lia).
  pose proof HB as (HB0 & HB1 & HBn).
  unfold acstr_at. split.
  - rewrite CT. unfold abytes. split; [lia|]. rewrite length_app, length_firstn. cbn [length]. split; [lia|].
    intros i Hi.
    destruct (Nat.lt_ge_cases i (Z.to_nat s)) as [Hlt|Hge].
    + rewrite nth_error_app1 by (rewrite length_firstn; lia).
      rewrite (lw_nth_error_firstn pay (Z.to_nat s) i Hlt).
      rewrite (HC (Z.of_nat i) ltac:(lia)). exact (HBn i ltac:(lia)).
    + assert (Ei : i = Z.to_nat s) by lia. subst i.
      rewrite nth_error_app2 by (rewrite length_firstn; lia).
      rewrite length_firstn. replace (Z.to_nat s - Nat.min (Z.to_nat s) (length pay))%nat with 0%nat by lia.
      cbn [nth_error]. rewrite <- HZ. f_equal. lia.
  - intros Hin. apply (cut_text_nonul pay n (zb 0) Hin). reflexivity.
Qed.

(* THE BUFFER stays a buffer: its bytes stay defined and writable when presence is kept. *)
Lemma ca_abuf_kept : forall (H : word -> bool) (m m2 : word -> option byte) out n,
  abuf segs (mrestrict H m) out n -> (forall x, apresent H m x -> apresent H m2 x) ->
  abuf segs (mrestrict H m2) out n.
Proof.
  intros H m m2 out n (junk & Hlen & (Hab & Hw)) Hp.
  pose proof Hab as (Ho & Hon & Hnth).
  exists (abytes_of segs (mrestrict H m2) out (length junk)).
  rewrite abytes_of_length. split; [exact Hlen|]. unfold au8arr. split.
  - apply abytes_of_abytes; [lia | lia |]. intros i Hi.
    destruct (nth_error junk i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
    rewrite <- (Hnth i Hi) in Eb. exact (lw_mbyte_some_kept segs H m m2 _ b Hp Eb).
  - rewrite abytes_of_length. unfold awrange. intros i Hi. apply (writable_kept (segs := segs) H m m2); [apply Hp | apply Hw; exact Hi].
Qed.

(* the region of one writable byte at atom nn (copy_attr's q = out + s3) *)
Lemma ca_region_ok_w1 : forall E m (nn : nat) q,
  bv_unsigned (ew E nn) = q -> 0 <= q -> q + 1 <= 2 ^ 64 -> writable_at segs m q ->
  region_ok segs E m (YP09.mkRegion (Some nn) 0 1 0 1 []).
Proof.
  intros E m nn q Hq H0 H1 Hw. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hq.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. replace (q + o) with q by lia. exact Hw.
Qed.

(* a shadow fact over a sub-range *)
Lemma ca_ra_sub : forall (rd : reader) x n y k,
  range_addressable rd SHADOW_OFF x n -> x <= y -> y + k <= x + n -> range_addressable rd SHADOW_OFF y k.
Proof. intros rd x n y k H H1 H2 z Hz. apply H. lia. Qed.

Lemma ca_hull_sub : forall (rd : reader) x n k,
  shadow_hull_vis rd x n -> 0 < k <= n -> shadow_hull_vis rd x k.
Proof.
  intros rd x n k H Hk s Hs. apply H. unfold shadow_addr in *. split; [lia|].
  assert (E1 : (x + k - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (E2 : (SHADOW_OFF + (x + k - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
  lia.
Qed.
End p.

(* ==========================================================================
   The symbolic states of the walk
   ========================================================================== *)
Definition ca_Bx : sv := SOff 32 0.
Definition ca_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ca_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 47 - 5) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)]
    [] [].
Definition ca_ss0 : sstate := mkSS AF_copy_attr sr_atoms [stack_region 48; got_regionP; bcell_regionP 32] None ca_facts0.
Definition ca_SH0 : list shent := [mkSHE 10 0 2].
Definition ca_attr_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 2 (SOff 33 0))].
Definition ca_out_region : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 1 [].
Definition ca_SH1 : list shent := [mkSHE 34 0 1].

(* environments *)
Lemma ag_trans : forall k E1 E2 E3, env_agree k E1 E2 -> env_agree k E2 E3 -> env_agree k E1 E3.
Proof. intros k E1 E2 E3 [A1 D1] [A2 D2]. split; [intros nn Hn; rewrite A2 by exact Hn; apply A1; exact Hn | congruence]. Qed.
Lemma ag_le : forall k k' E E', (k' <= k)%nat -> env_agree k E E' -> env_agree k' E E'.
Proof. intros k k' E E' Hk [A D]. split; [intros nn Hn; apply A; lia | exact D]. Qed.
Lemma ag_reg : forall regs EXT E (nn : nat) (r : bv 5),
  env_agree 35 (Ereg regs EXT) E -> Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r.
Proof.
  intros regs EXT E nn r [A _] Hr. pose proof (u5_range r) as R.
  rewrite A by lia. exact (ew_Ereg_nat regs EXT nn r Hr).
Qed.
Lemma ag_ext : forall regs EXT E (nn : nat) j,
  env_agree 35 (Ereg regs EXT) E -> nn = (32 + j)%nat -> (nn < 35)%nat -> ew E nn = nth j EXT (Z_to_bv 64 0).
Proof. intros regs EXT E nn j [A _] -> Hj. rewrite A by lia. exact (ew_Ereg_extra regs EXT j). Qed.
Lemma ag_ewset2 : forall E w w0, env_agree 512 E (ewset (ewset E 512 w) 513 w0).
Proof.
  intros E w w0. split; [|reflexivity].
  intros nn Hn. rewrite !ew_ewset_other by lia. reflexivity.
Qed.
Lemma ca_fds_wvb : forall l X m, m_fds (with_vm_backing l X m) = m_fds m.
Proof. intros l X m. exact (proj1 (wvb_fds_fs l X m)). Qed.
Lemma ca_fs_wvb : forall l X m, m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X m. exact (proj2 (wvb_fds_fs l X m)). Qed.
Lemma set_fs_self : forall S, S = set_fs (st_fs S) S.
Proof. intros [] ; reflexivity. Qed.
Lemma aarg_range : forall regs i, 0 <= aarg regs i < 2 ^ 64.
Proof. intros regs i. unfold aarg, argZ. apply u64_range. Qed.

(* the window kept by a run whose regions write only [lo, hi) and [lo2, hi2) *)
Ltac ca_frame_tac :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi x Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr;
     repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hrr end; lia|]);
  destruct Hin.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HV : LinkVals.
Hypothesis TL : PALib B.
Hypothesis ASTRNLEN : astrnlen_whole_realizesM pa_segs B 0x10360 0x10380 0x43048.
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy 0x52d78.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis TB : PcapSyms B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the 32 bytes 0x10360 .. 0x1037f the strnlen wrapper's word loop reads are read-only image bytes outside the
   runtime's statics and errno, so the Pre's arodata_okP shows them (lib/A/Rt/RtSStrlen.v sl_rom_in /
   sl_rom_unowned, the same computation) *)
Lemma ca_roc : forall x, 0x10360 <= x < 0x10380 ->
  in_rom pa_segs x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
Proof.
  intros x Hx. rewrite HSEGS. split.
  - assert (Hchk : match nth_error tfibsegs 0 with
      | Some s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? 0x10360) && (0x10380 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))
      | None => false end = true) by (vm_compute; reflexivity).
    destruct (nth_error tfibsegs 0) as [sg|] eqn:Esg; [|discriminate].
    apply andb_prop in Hchk as [Hchk Hhi]. apply andb_prop in Hchk as [Hw Hlo].
    apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
    exists sg. split; [exact (nth_error_In tfibsegs 0 Esg)|]. split; [exact Hw | lia].
  - assert (Hown : forallb (fun r : Z * Z => (0x10380 <=? fst r) || (fst r + snd r <=? 0x10360)) Tfib_owned_static = true)
      by (vm_compute; reflexivity).
    split.
    + intros HX. rewrite (ts_owned B TB) in HX. apply Exists_exists in HX as (r & Hr & Hin).
      rewrite forallb_forall in Hown. specialize (Hown r Hr).
      apply orb_prop in Hown as [H1|H1]; apply Z.leb_le in H1; unfold in_zr in Hin; lia.
    + rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia.
Qed.

(* the window of the journal is present at every memory the journal reaches *)
Lemma ca_win : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall x, sp0 - STK <= x < sp0 -> apresent (w_H W') mem' x.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k (_ & HXO & (memS & HJi & _) & _) x Hx.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. lia.
Qed.

(* The entry state: the frame, the .got slot of the shadow base and its cell, and the shadow entry of the length
   field's 2 bytes. *)
Lemma ca_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) EXT,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - COPY_ATTR_AK -> spZ regs <= sp0 ->
  nth 0 EXT (Z_to_bv 64 0) = Z_to_bv 64 SHADOW_OFF ->
  1 <= aarg regs 0 <= 2 ^ 47 - 5 ->
  aarg regs 0 + 2 <= kLowMemEnd - 1 \/ kHighMemBeg <= aarg regs 0 ->
  range_addressable (aview pa_segs (w_H W) memc) SHADOW_OFF (aarg regs 0) 2 ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regs EXT)) ca_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_copy_attr)) memc (seg_rom pa_segs))) /\
  sh_ok pa_segs ca_Bx ca_SH0 (Eimg (Ereg regs EXT)) (mrestrict (w_H W) memc).
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs EXT HJ Hal16 Hwlo Hwhi H32 Ha Hamr HRA.
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : COPY_ATTR_AK = 8240) by reflexivity. rewrite HK in Hwlo.
  destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  pose proof (pa_obj_img 64 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  pose proof (pa_val_range (A_OBJ 1)) as Vg. pose proof (pa_val_range (A_OBJ 64)) as Vc.
  unfold pcap_img_end, YImgTop.IMG_TOP in HcellR, HgotR.
  set (E := Eimg (Ereg regs EXT)).
  assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg regs EXT) nn)
    by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (eq_trans (ew_Ereg_extra regs EXT 0) H32)).
  assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (pa_val (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E (A_OBJ 64) = Z_to_bv 64 (pa_val (A_OBJ 64))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (U10 : bv_unsigned (ew E 10) = aarg regs 0)
    by (rewrite E10; unfold aarg, argZ; f_equal; f_equal; apply bv_eq; reflexivity).
  assert (VB : forall nn v, ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some nn) = v).
  { intros nn v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  split.
  - rewrite restrict_mkst_fx. unfold ca_ss0. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold stack_region, got_regionP, bcell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (lw_apresent_writable pa_segs). apply Hpres. lia.
      * fold E. rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) Egot Vg).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 1)) 0 8 (SOff (A_OBJ 64) 0) (pa_val (A_OBJ 64)));
          [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword_g pa_segs (w_H W) memc _ _ Kgot).
      * fold E. rewrite (VB (A_OBJ 64) (pa_val (A_OBJ 64)) Ecell Vc).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 64)) 0 8 ca_Bx SHADOW_OFF);
          [cbn [sv_denot ca_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; unfold SHADOW_OFF; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword_g pa_segs (w_H W) memc _ _ Kcell).
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      fold E. rewrite (VB (A_OBJ 1) (pa_val (A_OBJ 1)) Egot Vg), (VB (A_OBJ 64) (pa_val (A_OBJ 64)) Ecell Vc).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1a HcellR HgcD HgotR Hwlo Hwhi HSTK HXO.
      clear. intros. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [ca_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      fold E. rewrite Usp, U10, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO Hal16 Ha.
      clear. unfold SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - unfold sh_ok, ca_SH0. apply Forall_cons; [|apply Forall_nil].
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    assert (UB : U E ca_Bx = SHADOW_OFF) by (unfold ca_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
    assert (UA : U E (SOff 10 0) = aarg regs 0).
    { rewrite U_SOff, U10, Z.add_0_r. apply zcanon_id. unfold M64. lia. }
    fold E. rewrite UB, UA. split.
    + rewrite Z.add_0_r, Z.sub_0_r. rewrite <- (aview_rd_of pa_segs). exact HRA.
    + intros x Hx. unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* the write obligation of a run whose regions write only the frame (based at sp, Usx) *)
Ltac ca_awr Usx :=
  repeat (apply awr_ok_x_cons; [let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
    first [lia | rewrite Usx in Hx; left; split; [left; lia | lia]] |]);
  apply awr_ok_x_nil.

Theorem copy_attr_aproof : forall rlo rhi, copy_attr_acontract SK pa_segs rlo rhi B.
Proof.
intros rlo rhi. unfold copy_attr_acontract, aleaf_rd.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE _ HP.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : COPY_ATTR_AK = 8240) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & _ & Hajw & _).
pose proof HJ as HJ0.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear memS HJi Hstk.
unfold copy_attr_apre in HP.
destruct HP as (l & pay & HU & Hl & HPAY & Hlen & Ha0 & Hamr & Hapf & HRA2 & HRAP & HHULLP & _ & HOUT).
unfold copy_attr_awr, copy_attr_apost in *.
unfold RTA_HDR in *.
rewrite HK in Hwlo.
pose proof (aarg_range regs 0) as Ra. pose proof (aarg_range regs 1) as Rout. pose proof (aarg_range regs 2) as Rn.
set (a := aarg regs 0) in *. set (out := aarg regs 1) in *. set (n := aarg regs 2) in *.
assert (Hsp_lo : alloc_ceiling + 8240 <= spZ regs) by lia.
assert (Hsp_hi : spZ regs <= 2 ^ 47) by lia.
unfold amem_range in Hamr.
unfold apart_frame in Hapf. rewrite HK in Hapf.
pose proof (nul_at_le pay) as NL.
set (s3v := Z.min (Z.of_nat (nul_at pay)) (n - 1)).
set (q := out + s3v).
set (EXT := [w64 SHADOW_OFF; w64 l; w64 q]).
assert (Eq_s3 : s3v = Z.min (Z.of_nat (nul_at pay)) (n - 1)) by reflexivity.
assert (Eq_q : q = out + s3v) by reflexivity.
assert (G10 : getr regs 10%bv = w64 a) by (unfold a, aarg, argZ, w64; rewrite Z_to_bv_bv_unsigned; f_equal; apply bv_eq; reflexivity).
assert (G11 : getr regs 11%bv = w64 out) by (unfold out, aarg, argZ, w64; rewrite Z_to_bv_bv_unsigned; f_equal; apply bv_eq; reflexivity).
assert (G12 : getr regs 12%bv = w64 n) by (unfold n, aarg, argZ, w64; rewrite Z_to_bv_bv_unsigned; f_equal; apply bv_eq; reflexivity).
(* the payload's bytes, as the view at the entry memory shows them *)
assert (HPV : forall i, 0 <= i < Z.of_nat (length pay) ->
  aview pa_segs (w_H W) memc (a + 4 + i) = option_map (fun b : byte => bv_unsigned b) (nth_error pay (Z.to_nat i))).
{ intros i Hi. pose proof HPAY as (_ & _ & HBn). unfold aview.
  replace (a + 4 + i) with (a + 4 + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (HBn (Z.to_nat i) ltac:(lia)). reflexivity. }
destruct (ca_entry G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs EXT HJ Hal16
  ltac:(rewrite HK; exact Hwlo) Hwhi eq_refl ltac:(change (aarg regs 0) with a; lia)
  ltac:(change (aarg regs 0) with a; lia) HRA2) as [HS SHOK].
remember (Eimg (Ereg regs EXT)) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 35 (Ereg regs EXT) E)
  by (subst E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HEdef.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (ag_reg regs EXT E 2 2%bv HAE eq_refl); reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 out) by (rewrite (ag_reg regs EXT E 11 11%bv HAE eq_refl); exact G11).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (rewrite (ag_reg regs EXT E 12 12%bv HAE eq_refl); exact G12).
assert (HCFG : cfg_at pa_segs COPY_ATTR_A regs memc mdc =
  mkCfg (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_copy_attr)) memc (seg_rom pa_segs)) mdc).
{ unfold cfg_at. rewrite (lv_text HV). reflexivity. }
rewrite HCFG. clear HCFG.
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (RUNTO := paj_run_to_x SK B LAWS G HGok XO OUT).
pose (BR := paj_branch (PI := PI)).
pose (RET := paj_ret_at (PL := PL_link) (PI := PI)).
(* +0x00 .. +0x1c: the frame, the saves, `beqz a1` *)
paj_run_tok RUN HS HJ SHOK ca_span.
{ unfold ca_ss0. cbn [ss_mem].
  repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP bcell_regionP] in Hx;
    first [lia | rewrite Usp in Hx; left; split; [left; lia | lia]] |]).
  apply awr_ok_x_nil. }
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ regs - 8240 <= x < spZ regs) HFr ltac:(ca_frame_tac)) as UN1.
pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK ca_span.
- (* out = 0: the epilogue and the `ret` (path A) *)
  rewrite branch_eq_U, (U_atom E 11 out E11 Rout), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK ca_span.
  { repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
      first [lia | rewrite Usp in Hx; left; split; [left; lia | lia]] |]).
    apply awr_ok_x_nil. }
  pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ regs - 8240 <= x < spZ regs) HFr ltac:(ca_frame_tac)) as UN2.
  pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P2.
  clear HF HFr HG.
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    prreg HS (1%bv : bv 5) R1;
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros mat';
    rewrite R1, (ag_reg regs EXT E 1 1%bv HAE eq_refl), Hraw;
    eapply (apost_leaf_app SK pa_segs B LAWS pa_segs_low COPY_ATTR_AK 0 _ G XO OUT STK sp0 FP ly S W0 mem0 md0 own
      lyc Sc W memc mdc k regs (ms_regs msc) (ms_mem msc) _ _ HJ0);
    [ apply (ajournal_gx_materialize pa_segs B LAWS pa_segs_low); exact HJ
    | lia | rewrite HK; lia | rewrite HK; lia
    | rewrite ?ca_fds_wvb; reflexivity
    | rewrite ?ca_fs_wvb; reflexivity
    | eapply (aregs_preserved_of_st_ok pa_segs _ E _ _ regs EXT HS); [exact (ag_le 35 32 _ _ ltac:(lia) HAE) | vm_compute; reflexivity]
    | intros x Hx Hw _; rewrite HK in Hw; rewrite (UN2 x Hx Hw); exact (UN1 x Hx Hw)
    | intros x Hp; exact (P2 x (P1 x Hp))
    | intros x Hx; rewrite HK in Hx; apply (ca_win G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k HJ); lia
    | intros x (r & Hr & Hx); destruct Hr as [<- | []]; unfold aivl in Hx; cbn [fst snd] in Hx; rewrite Hc in Hx; cbn in Hx; lia
    | cbv beta; split; [apply set_fs_self|]; split; [apply Permutation_refl|];
      split; intros Hout0; exfalso; exact (Hout0 Hc) ]
  end.
- (* out <> 0 *)
  rewrite branch_eq_U, (U_atom E 11 out E11 Rout), U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hout0.
  paj_run_tok RUN HS HJ SHOK ca_span.
  { repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
      first [lia | rewrite Usp in Hx; left; split; [left; lia | lia]] |]).
    apply awr_ok_x_nil. }
  pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ regs - 8240 <= x < spZ regs) HFr ltac:(ca_frame_tac)) as UN2.
  pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P2.
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (UN12 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 8240 <= x < spZ regs) ->
      aview pa_segs (w_H W) (ms_mem msx) x = aview pa_segs (w_H W) memc x)
      by (let x := fresh "x" in let Hx := fresh "Hx" in let Hw := fresh "Hw" in
          intros x Hx Hw; rewrite (UN2 x Hx Hw); exact (UN1 x Hx Hw));
    assert (P12 : forall x, apresent (w_H W) memc x -> apresent (w_H W) (ms_mem msx) x)
      by (let x := fresh "x" in let Hp := fresh "Hp" in intros x Hp; exact (P2 x (P1 x Hp)))
  end; clear UN1 P1 UN2 P2.
  psrr_branch_tok RUN BR HS SHOK ca_span.
  + (* n = 0: the epilogue and the `ret` (path B) *)
    rewrite branch_eq_U, (U_atom E 12 n E12 Rn), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ SHOK ca_span.
    { repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
        first [lia | rewrite Usp in Hx; left; split; [left; lia | lia]] |]).
      apply awr_ok_x_nil. }
    pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ regs - 8240 <= x < spZ regs) HFr ltac:(ca_frame_tac)) as UN3.
    pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P3.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      prreg HS (1%bv : bv 5) R1;
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros mat';
      rewrite R1, (ag_reg regs EXT E 1 1%bv HAE eq_refl), Hraw;
      eapply (apost_leaf_app SK pa_segs B LAWS pa_segs_low COPY_ATTR_AK 0 _ G XO OUT STK sp0 FP ly S W0 mem0 md0 own
        lyc Sc W memc mdc k regs (ms_regs msc) (ms_mem msc) _ _ HJ0);
      [ apply (ajournal_gx_materialize pa_segs B LAWS pa_segs_low); exact HJ
      | lia | rewrite HK; lia | rewrite HK; lia
      | rewrite ?ca_fds_wvb; reflexivity
      | rewrite ?ca_fs_wvb; reflexivity
      | eapply (aregs_preserved_of_st_ok pa_segs _ E _ _ regs EXT HS); [exact (ag_le 35 32 _ _ ltac:(lia) HAE) | vm_compute; reflexivity]
      | intros x Hx Hw _; rewrite HK in Hw; rewrite (UN3 x Hx Hw); exact (UN12 x Hx Hw)
      | intros x Hp; exact (P3 x (P12 x Hp))
      | intros x Hx; rewrite HK in Hx; apply (ca_win G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k HJ); lia
      | intros x (r & Hr & Hx); destruct Hr as [<- | []]; unfold aivl in Hx; cbn [fst snd] in Hx;
        rewrite Hc in Hx; destruct (out =? 0); cbn in Hx; lia
      | cbv beta; split; [apply set_fs_self|]; split; [apply Permutation_refl|];
        split; intros _ Hn1; exfalso; lia ]
    end.
  + (* out <> 0 and n >= 1 (path C) *)
    rewrite branch_eq_U, (U_atom E 12 n E12 Rn), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    assert (Hn1 : 1 <= n) by lia. clear Hc.
    destruct (HOUT Hout0 Hn1) as (Hapfo & Happ & Habuf & Hamro & HRAO & HHULLO). clear HOUT.
    unfold apart_frame in Hapfo. rewrite HK in Hapfo. unfold apart in Happ. unfold amem_range in Hamro.
    assert (Hs3 : 0 <= s3v <= n - 1) by lia.
    assert (Hs3l : s3v <= l - 4) by lia.
    assert (Hq : 1 <= q <= 2 ^ 47 - 2) by lia.
    assert (Wr_in : forall x, out <= x < out + n -> inFP [aivl out n] x).
    { intros x Hx. exists (aivl out n). split; [left; reflexivity|]. unfold aivl. cbn [fst snd].
      destruct (Z.eqb_spec out 0); [lia | exact Hx]. }
    (* +0x28 .. +0x48: the shadow base, the check of the length field *)
    paj_run_to_tok RUNTO HS HJ SHOK ca_span (AF_copy_attr + 0x48).
    { repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
        first [lia | rewrite Usp in Hx; left; split; [left; lia | lia]] |]).
      apply awr_ok_x_nil. }
    pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ regs - 8240 <= x < spZ regs) HFr ltac:(ca_frame_tac)) as UN3.
    pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P3.
    clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in * end.
    assert (HA1 : env_agree 512 E E1) by (subst E1; apply ag_ewset2).
    clearbody E1.
    assert (HAE1 : env_agree 35 (Ereg regs EXT) E1) by (exact (ag_trans _ _ _ _ HAE (ag_le 512 35 _ _ ltac:(lia) HA1))).
    assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite (ag_reg regs EXT E1 2 2%bv HAE1 eq_refl); reflexivity).
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (UN13 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 8240 <= x < spZ regs) ->
        aview pa_segs (w_H W) (ms_mem msx) x = aview pa_segs (w_H W) memc x)
        by (let x := fresh "x" in let Hx := fresh "Hx" in let Hw := fresh "Hw" in
            intros x Hx Hw; rewrite (UN3 x Hx Hw); exact (UN12 x Hx Hw));
      assert (P13 : forall x, apresent (w_H W) memc x -> apresent (w_H W) (ms_mem msx) x)
        by (let x := fresh "x" in let Hp := fresh "Hp" in intros x Hp; exact (P3 x (P12 x Hp)))
    end; clear UN12 P12 UN3 P3.
    (* the .got regions out, the length field in *)
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
      let rs := eval vm_compute in (firstn 1 (ss_mem ssx)) in
      pose proof (st_ok_pi_keep pa_segs pa_val E1 ssx _ rs HS
        ltac:(vm_compute; apply submem_keep; [apply subregion_refl | apply submem_nil]) ltac:(vm_compute; reflexivity)) as HS3
    end.
    clear HS.
    lazymatch type of HS3 with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      pose proof (st_ok_pi_add_region E1 ssx _ ca_attr_region HS3 eq_refl) as HS4
    end.
    clear HS3.
    lazymatch type of HS4 with ?t -> ?u -> _ => assert (HR4 : t); [|specialize (HS4 HR4); clear HR4] end.
    { unfold region_ok, ca_attr_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
      rewrite (ag_reg regs EXT E1 10 10%bv HAE1 eq_refl), G10. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val pa_segs E1 _ a 0 2 (SOff 33 0) l);
        [ cbn [sv_denot]; rewrite (ag_ext regs EXT E1 33 1 HAE1 eq_refl ltac:(lia)); unfold EXT; cbn [nth];
          unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
        | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. change (N.to_nat 2) with 2%nat. intros kk Hkk.
      transitivity (mbyte pa_segs (mrestrict (w_H W) memc) (a + Z.of_nat kk)); [|exact (HU kk Hkk)].
      apply (lw_mbyte_of_aview pa_segs). apply UN13; lia. }
    lazymatch type of HS4 with ?t -> _ => assert (HR4 : t); [|specialize (HS4 HR4); clear HR4] end.
    { assert (B10 : base_val E1 (Some 10%nat) = a).
      { cbn [base_val]. rewrite (ag_reg regs EXT E1 10 10%bv HAE1 eq_refl), G10. unfold w64. apply unsigned_lit_small. lia. }
      assert (B2 : base_val E1 (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp1).
      cbv [ss_mem all_disjoint extent_disjoint ca_attr_region YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite B10, B2. split; [lia | exact I]. }
    pose proof (st_ok_pi_add_fact E1 _ _ 33 (mkAF 4 65535 0) HS4) as HS.
    lazymatch type of HS with ?t -> _ => assert (HR4 : t); [|specialize (HS HR4); clear HR4] end.
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (ag_ext regs EXT E1 33 1 HAE1 eq_refl ltac:(lia)). unfold EXT; cbn [nth].
      unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
    clear HS4.
    lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
    clear SHOK.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      assert (SHOK : sh_ok pa_segs ca_Bx [] E1 (mrestrict (w_H W) (ms_mem msx))) by (apply Forall_nil) end.
    (* +0x48 .. +0x58: `lhu`, the arguments, the call of wrapper_strnlen *)
    paj_run_tok RUN HS HJ SHOK ca_span.
    { repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
        first [lia | rewrite Usp1 in Hx; left; split; [left; lia | lia]] |]).
      apply awr_ok_x_nil. }
    pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ regs - 8240 <= x < spZ regs) HFr ltac:(ca_frame_tac)) as UN4.
    pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P4.
    clear HF HFr HG.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (UN14 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 8240 <= x < spZ regs) ->
        aview pa_segs (w_H W) (ms_mem msx) x = aview pa_segs (w_H W) memc x)
        by (let x := fresh "x" in let Hx := fresh "Hx" in let Hw := fresh "Hw" in
            intros x Hx Hw; rewrite (UN4 x Hx Hw); exact (UN13 x Hx Hw));
      assert (P14 : forall x, apresent (w_H W) memc x -> apresent (w_H W) (ms_mem msx) x)
        by (let x := fresh "x" in let Hp := fresh "Hp" in intros x Hp; exact (P4 x (P13 x Hp)))
    end; clear UN13 P13 UN4 P4.
    pmkst HS.
    prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
    prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
    rewrite (lv_sigma HV). change (link_sigma LS___interceptor_trampoline_strnlen) with 0x43048.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      assert (Q3 : getr rg 3 = w64 (as_gp B)) by (rewrite R3, (ag_reg regs EXT E1 3 3%bv HAE1 eq_refl); exact Hgp);
      assert (Q4 : getr rg 4 = w64 (as_tp B)) by (rewrite R4, (ag_reg regs EXT E1 4 4%bv HAE1 eq_refl); exact Htp);
      assert (Qsp : spZ rg = spZ regs - 48)
        by (unfold spZ at 1; rewrite R2, Usp1, unsigned_lit_small by lia; reflexivity);
      assert (Q10 : getr rg 10 = w64 (a + 4))
        by (rewrite R10, (ag_reg regs EXT E1 10 10%bv HAE1 eq_refl), G10; unfold w64; rewrite unsigned_lit_small by lia; reflexivity);
      assert (Q11 : getr rg 11 = w64 (l - 4))
        by (rewrite R11, (ag_ext regs EXT E1 33 1 HAE1 eq_refl ltac:(lia)); unfold EXT; cbn [nth]; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia);
      assert (HVM : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 8240 <= x < spZ regs) ->
        aview pa_segs (w_H W) mm x = aview pa_segs (w_H W) memc x) by exact UN14
    end.
    clear R2 R3 R4 R10 R11.
    eapply SRr_bind.
    { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
        eapply (aj_gx_strnlen_atS SK pa_segs B LAWS pa_segs_low 0x10360 0x10380 0x43048 ASTRNLEN
          G XO OUT W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (a + 4) (l - 4) _ HGok HJ);
        [ rewrite Qsp; lia | rewrite Qsp; lia | rewrite Qsp; lia
        | exact Q3 | exact Q4 | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
        | exact Q10 | exact Q11 | lia | lia | lia
        | intros x Hx; split; [|rewrite Qsp; lia];
          rewrite (HVM x ltac:(lia) ltac:(lia)); replace x with (a + 4 + (x - (a + 4))) by lia;
          rewrite (HPV (x - (a + 4)) ltac:(lia)); destruct (nth_error pay (Z.to_nat (x - (a + 4)))) eqn:Eb;
          [discriminate | apply nth_error_None in Eb; lia]
        | intros x Hx; rewrite Qsp; lia
        | unfold amem_range; lia
        | eapply (range_addressable_kept_win _ _ (spZ regs - 8240) (spZ regs));
          [ intros s Hs Hns; apply HVM; [exact Hs | exact Hns] | lia | lia | lia | exact HRAP ]
        | intros Hpos; eapply (shadow_hull_vis_kept_win _ _ (spZ regs - 8240) (spZ regs));
          [ intros s Hs Hns; apply HVM; [exact Hs | exact Hns] | lia | lia | lia | lia | exact (HHULLP Hpos) ]
        | intros x Hx; destruct (ca_roc x Hx) as (Hrom & Hno & Her);
          rewrite (HVM x ltac:(lia) ltac:(lia)); exact (HROD x (or_introl Hrom) Hno Her) ]
      end. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (j & HFB & Hj) & Hfr2 & Hpres2 & Hsm2).
    assert (FD2 : m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc).
    { unfold same_but_materialized in Hsm2. rewrite Hsm2.
      rewrite ?ca_fds_wvb, ?ca_fs_wvb. split; reflexivity. }
    clear Hsm2.
    (* the answer is nul_at of the payload *)
    assert (Hjn : j = Z.of_nat (nul_at pay)).
    { lazymatch type of HFB with first_byte _ _ ?mm _ _ _ _ =>
        destruct HFB as (HF0 & HF1 & HF2);
        apply (ca_first_nul pay (aview pa_segs (w_H W) mm) (a + 4) j) end.
      - intros i Hi. rewrite HVM by lia. exact (HPV i Hi).
      - lia.
      - exact HF1.
      - intros Hlt. apply HF2. lia. }
    jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [1]%nat HS2.
    lazymatch type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp1; intros x Hx.
      - apply (lw_mbyte_of_aview pa_segs). apply Hfr2; [lia | rewrite Qsp; lia].
      - intros _. apply (lw_apresent_writable pa_segs). apply (ca_win G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k HJ2). lia. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    remember (havoc E1 35 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
    assert (HEIc2 : img_env pa_val A_LIM E2) by (rewrite HE2; apply img_env_havoc; [assumption | cbv; lia]).
    assert (HAE2 : env_agree 35 (Ereg regs EXT) E2) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
    assert (H39 : ew E2 39 = getr regs2 10%bv) by (rewrite HE2; reflexivity).
    clear HE2.
    assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite (ag_reg regs EXT E2 2 2%bv HAE2 eq_refl); reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
    clear SHOK.
    assert (SHOK : sh_ok pa_segs ca_Bx [] E2 (mrestrict (w_H W) mem2)) by (apply Forall_nil).
    assert (UN15 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 8240 <= x < spZ regs) ->
      aview pa_segs (w_H W) mem2 x = aview pa_segs (w_H W) memc x)
      by (intros x Hx Hw; rewrite (Hfr2 x Hx ltac:(rewrite Qsp; lia)); exact (HVM x Hx Hw)).
    assert (P15 : forall x, apresent (w_H W) memc x -> apresent (w_H W) mem2 x)
      by (intros x Hp; exact (Hpres2 x (P14 x Hp))).
    clear HVM Hfr2 P14 Hpres2 R1 Q3 Q4 Q10 Q11 Qsp.
    (* +0x5c .. +0x60: the cap *)
    paj_run_tok RUN HS HJ2 SHOK ca_span.
    { repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
        first [lia | rewrite Usp2 in Hx; left; split; [left; lia | lia]] |]).
      apply awr_ok_x_nil. }
    pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ regs - 8240 <= x < spZ regs) HFr ltac:(ca_frame_tac)) as UN6.
    pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P6.
    clear HF HFr HG.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (UN16 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 8240 <= x < spZ regs) ->
        aview pa_segs (w_H W) (ms_mem msx) x = aview pa_segs (w_H W) memc x)
        by (let x := fresh "x" in let Hx := fresh "Hx" in let Hw := fresh "Hw" in
            intros x Hx Hw; rewrite (UN6 x Hx Hw); exact (UN15 x Hx Hw));
      assert (P16 : forall x, apresent (w_H W) memc x -> apresent (w_H W) (ms_mem msx) x)
        by (let x := fresh "x" in let Hp := fresh "Hp" in intros x Hp; exact (P6 x (P15 x Hp)))
    end; clear UN15 P15 UN6 P6.
    assert (U39 : U E2 (SOff 39 0) = j)
      by (apply U_atom; [rewrite H39; exact Hj | subst j; lia]).
    assert (U12 : U E2 (SOff 12 0) = n)
      by (apply U_atom; [rewrite (ag_reg regs EXT E2 12 12%bv HAE2 eq_refl); exact G12 | lia]).
    psrr_branch_tok RUN BR HS SHOK ca_span.
    * (* j < n: s3 = j *)
      rewrite branch_ltu_U, U39, U12 in Hc. apply Z.ltb_lt in Hc.
      assert (Es3 : s3v = j) by lia.
      (* +0x68 .. +0x74: the arguments of checked_memcpy; the call; the alias out + j = q; +0x78 .. +0xac *)
      paj_run_tok RUN HS HJ2 SHOK ca_span; [ca_awr Usp2 |];
      let UN7 := fresh "UN7" in let P7 := fresh "P7" in
      pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ regs - 8240 <= x < spZ regs) HFr ltac:(ca_frame_tac)) as UN7;
      pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P7;
      clear HF HFr HG;
      pmkst HS;
      prreg HS (1%bv : bv 5) R1; prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
      prreg HS (10%bv : bv 5) R10; prreg HS (11%bv : bv 5) R11; prreg HS (12%bv : bv 5) R12;
      rewrite (lv_sigma HV); change (link_sigma LS___asan_memcpy) with 0x52d78;
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
        assert (Q3 : getr rg 3 = w64 (as_gp B)) by (rewrite R3, (ag_reg regs EXT E2 3 3%bv HAE2 eq_refl); exact Hgp);
        assert (Q4 : getr rg 4 = w64 (as_tp B)) by (rewrite R4, (ag_reg regs EXT E2 4 4%bv HAE2 eq_refl); exact Htp);
        assert (Qsp : spZ rg = spZ regs - 48)
          by (unfold spZ at 1; rewrite R2, Usp2, unsigned_lit_small by lia; reflexivity);
        assert (Q10 : getr rg 10 = w64 out) by (rewrite R10, (ag_reg regs EXT E2 11 11%bv HAE2 eq_refl); exact G11);
        assert (Q11 : getr rg 11 = w64 (a + 4))
          by (rewrite R11, (ag_reg regs EXT E2 10 10%bv HAE2 eq_refl), G10; unfold w64; rewrite unsigned_lit_small by lia; reflexivity);
        assert (Q12 : getr rg 12 = w64 s3v) by (rewrite R12; (rewrite H39, Hj, Es3; reflexivity));
        assert (HVM : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 8240 <= x < spZ regs) ->
          aview pa_segs (w_H W) mm x = aview pa_segs (w_H W) memc x)
          by (intros x Hx Hw; rewrite (UN7 x Hx Hw); exact (UN16 x Hx Hw));
        assert (HPM : forall x, apresent (w_H W) memc x -> apresent (w_H W) mm x)
          by (intros x Hp; exact (P7 x (P16 x Hp)));
        assert (FDy : m_fds mdx = m_fds mdc /\ m_fs mdx = m_fs mdc)
          by (rewrite ?ca_fds_wvb, ?ca_fs_wvb; exact FD2)
      end;
      clear R2 R3 R4 R10 R11 R12 UN7 P7.
      eapply SRr_bind;
      [ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
          eapply (aj_gx_intrin_at SK pa_segs B LAWS pa_segs_low OCpy 0x52d78 AMEMCPY
            G XO OUT W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k out (a + 4) s3v _ HGok HJ2 Q10 Q11 Q12);
          [ lia | lia | lia
          | rewrite Qsp; lia | rewrite Qsp; lia | rewrite Qsp; lia
          | exact Q3 | exact Q4 | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
          | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
            let Haw := fresh "Haw" in let Hxo := fresh "Hxo" in let HGx := fresh "HGx" in let Hox := fresh "Hox" in
            destruct (Hajw x (Wr_in x ltac:(lia))) as [[Haw Hxo] | [HGx | Hox]];
            [ left; split; [exact Haw | split; [exact Hxo | rewrite Qsp; lia]]
            | right; left; split; [exact HGx|];
              apply (writable_kept (segs := pa_segs) (w_H W) memc mm x (HPM x));
              let junk := fresh "junk" in let Hjl := fresh "Hjl" in let Hwr := fresh "Hwr" in
              destruct Habuf as (junk & Hjl & (_ & Hwr)); replace x with (out + (x - out)) by lia; apply Hwr; lia
            | right; right; exact Hox ]
          | unfold amem_range; lia
          | eapply (range_addressable_kept_win _ _ (spZ regs - 8240) (spZ regs));
            [ intros ?s ?Hs ?Hns; apply HVM; assumption | lia | lia | lia
            | exact (ca_ra_sub _ out n out s3v HRAO ltac:(lia) ltac:(lia)) ]
          | intros ?Hpos; eapply (shadow_hull_vis_kept_win _ _ (spZ regs - 8240) (spZ regs));
            [ intros ?s ?Hs ?Hns; apply HVM; assumption | lia | lia | lia | lia
            | exact (ca_hull_sub _ out n s3v HHULLO ltac:(lia)) ]
          | split; [lia|]; split; [lia|]; split;
            [ let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; split; [|rewrite Qsp; lia];
              rewrite (HVM x ltac:(lia) ltac:(lia)); replace x with (a + 4 + (x - (a + 4))) by lia;
              rewrite (HPV (x - (a + 4)) ltac:(lia));
              let Eb := fresh "Eb" in
              destruct (nth_error pay (Z.to_nat (x - (a + 4)))) eqn:Eb;
              [discriminate | apply nth_error_None in Eb; lia]
            |];
            split; [lia|]; split; [unfold amem_range; lia|]; split;
            [ eapply (range_addressable_kept_win _ _ (spZ regs - 8240) (spZ regs));
              [ intros ?s ?Hs ?Hns; apply HVM; assumption | lia | lia | lia
              | exact (ca_ra_sub _ (a + 4) (l - 4) (a + 4) s3v HRAP ltac:(lia) ltac:(lia)) ]
            | intros ?Hpos; eapply (shadow_hull_vis_kept_win _ _ (spZ regs - 8240) (spZ regs));
              [ intros ?s ?Hs ?Hns; apply HVM; assumption | lia | lia | lia | lia
              | exact (ca_hull_sub _ (a + 4) (l - 4) s3v (HHULLP ltac:(lia)) ltac:(lia)) ] ] ]
        end
      | ].
      cbv beta; intros ? ? _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hd3 & Hcpy & Hfr3 & Hpres3 & Hsm3);
      cbv iota in Hcpy;
      assert (FD3 : m_fds md3 = m_fds mdc /\ m_fs md3 = m_fs mdc)
        by (unfold same_but_materialized in Hsm3; rewrite Hsm3;
            rewrite ?ca_fds_wvb, ?ca_fs_wvb; exact FDy);
      clear Hsm3;
      jafter_call_keep_pi HS 51%nat regs3 (mrestrict (w_H W) mem3) HP3 [0]%nat HS3;
      (lazymatch type of HS3 with ?tq -> _ => let HRK := fresh "HRK" in assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end);
      [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
        split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp2; intros ? ?;
        [ apply (lw_mbyte_of_aview pa_segs); apply Hfr3; [lia | lia | rewrite Qsp; lia]
        | intros _; apply (lw_apresent_writable pa_segs);
          apply (ca_win G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k HJ3); lia ]
      | ];
      clear HS; rewrite <- restrict_mkst_fx in HS3; rename HS3 into HS;
      remember (havoc E2 51 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS;
      assert (HEIc3 : img_env pa_val A_LIM E3) by (rewrite HE3; apply img_env_havoc; [assumption | cbv; lia]);
      assert (HA23 : env_agree 51 E2 E3) by (rewrite HE3; apply env_agree_havoc_ge; [lia | apply env_agree_refl]);
      clear HE3;
      assert (HAE3 : env_agree 35 (Ereg regs EXT) E3) by (exact (ag_trans _ _ _ _ HAE2 (ag_le 51 35 _ _ ltac:(lia) HA23)));
      assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite (ag_reg regs EXT E3 2 2%bv HAE3 eq_refl); reflexivity);
      assert (F11 : ew E3 11 = Z_to_bv 64 out) by (rewrite (ag_reg regs EXT E3 11 11%bv HAE3 eq_refl); exact G11);
      assert (F12 : ew E3 12 = Z_to_bv 64 n) by (rewrite (ag_reg regs EXT E3 12 12%bv HAE3 eq_refl); exact G12);
      assert (F39 : ew E3 39 = Z_to_bv 64 j) by (rewrite (proj1 HA23 39%nat ltac:(lia)), H39; exact Hj);
      assert (F34 : ew E3 34 = Z_to_bv 64 q) by (exact (ag_ext regs EXT E3 34 2 HAE3 eq_refl ltac:(lia)));
      assert (F32 : ew E3 32 = Z_to_bv 64 SHADOW_OFF) by (exact (ag_ext regs EXT E3 32 0 HAE3 eq_refl ltac:(lia)));
      assert (U34 : bv_unsigned (ew E3 34) = q) by (rewrite F34; apply unsigned_lit_small; lia);
      let HS5 := fresh "HS5" in
      pose proof (st_ok_pi_add_alias pa_segs pa_val E3 _ _ (SAlu ALU_ADD (SOff 11 0) (SOff 39 0)) (SOff 34 0) HS) as HS5;
      (lazymatch type of HS5 with ?t -> _ => let HR := fresh "HR" in assert (HR : t) by (apply U_inj; rewrite U_SAlu; cbn [zalu_raw];
                  rewrite (U_atom E3 11 out F11 Rout), (U_atom E3 39 j F39 ltac:(lia)), (U_atom E3 34 q F34 ltac:(lia));
                  unfold zcanon, M64; rewrite Z.mod_small by lia; lia); specialize (HS5 HR); clear HR end);
      clear HS;
      let HS6 := fresh "HS6" in
      pose proof (st_ok_pi_add_fact E3 _ _ 34 (mkAF 1 (2 ^ 47 - 2) 0) HS5) as HS6;
      (lazymatch type of HS6 with ?t -> _ => let HR := fresh "HR" in
         assert (HR : t) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U34, Z.pow_0_r, Z.mod_1_r; lia);
         specialize (HS6 HR); clear HR end);
      clear HS5;
      (lazymatch type of HS6 with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS6 end);
      let HS7 := fresh "HS7" in
      pose proof (st_ok_pi_add_region E3 _ _ ca_out_region HS6 eq_refl) as HS7;
      (lazymatch type of HS7 with ?t -> _ -> _ => let HR := fresh "HR" in assert (HR : t);
         [ refine (ca_region_ok_w1 pa_segs E3 _ 34 q U34 ltac:(lia) ltac:(lia) _);
           cbn [ms_mem restrict mkst];
           replace q with (out + (q - out)) by lia;
           apply (writable_kept (segs := pa_segs) (w_H W) memc mem3 _ (fun Hp => Hpres3 _ (HPM _ Hp)));
           let junk := fresh "junk" in let Hjl := fresh "Hjl" in let Hwr := fresh "Hwr" in
           destruct Habuf as (junk & Hjl & (_ & Hwr)); apply Hwr; lia
         | specialize (HS7 HR); clear HR ] end);
      (lazymatch type of HS7 with ?t -> _ => let HR := fresh "HR" in assert (HR : t);
         [ assert (B34 : base_val E3 (Some 34%nat) = q) by (cbn [base_val]; exact U34);
           assert (B2 : base_val E3 (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp3);
           cbv [ss_mem all_disjoint extent_disjoint ca_out_region YP09.r_base YP09.r_lo YP09.r_hi];
           rewrite B34, B2; split; [lia | exact I]
         | specialize (HS7 HR); clear HR ] end);
      clear HS6; rename HS7 into HS;
      (lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end);
      clear SHOK;
      assert (SHOK3 : sh_ok pa_segs ca_Bx ca_SH1 E3 (mrestrict (w_H W) mem3));
      [ unfold sh_ok, ca_SH1; apply Forall_cons; [|apply Forall_nil];
        unfold shent_ok, app_apart, ca_Bx; cbn [she_m she_lo she_hi];
        rewrite (U_atom E3 32 SHADOW_OFF F32 ltac:(unfold SHADOW_OFF; lia)), (U_atom E3 34 q F34 ltac:(lia)); split;
        [ rewrite Z.add_0_r, Z.sub_0_r; rewrite <- (aview_rd_of pa_segs);
          apply (ra_shadow_eq (aview pa_segs (w_H W) memc));
          [ exact (ca_ra_sub _ out n q 1 HRAO ltac:(lia) ltac:(lia))
          | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
            pose proof (shadow_addr_bounds x ltac:(unfold kHighMemEnd; lia)) as ?Hsb;
            etransitivity;
            [ apply Hfr3; [unfold kHighShadowEnd in *; lia | unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; lia
                          | rewrite Qsp; unfold kHighShadowEnd in *; lia]
            | apply HVM; unfold kHighShadowEnd in *; lia ] ]
        | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia ]
      | ].
      paj_run_tok RUN HS HJ3 SHOK3 ca_span;
      [ repeat (apply awr_ok_x_cons; [let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
          first [lia | rewrite Usp3 in Hx; left; split; [left; lia | lia]
                | rewrite U34 in Hx; exact (Hajw x (Wr_in x ltac:(lia)))] |]);
        apply awr_ok_x_nil
      | ];
      (lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E4 := Ex) in * end);
      assert (HA34 : env_agree 512 E3 E4) by (subst E4; apply ag_ewset2);
      clearbody E4;
      assert (HAE4 : env_agree 35 (Ereg regs EXT) E4) by (exact (ag_trans _ _ _ _ HAE3 (ag_le 512 35 _ _ ltac:(lia) HA34)));
      let UN8 := fresh "UN8" in let P8 := fresh "P8" in
      pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => (spZ regs - 8240 <= x < spZ regs) \/ x = q) HFr
        ltac:(ca_frame_tac)) as UN8;
      pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P8;
      clear HF HFr HG;
      lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
        prreg HS (1%bv : bv 5) R1f;
        let r0 := eval vm_compute in (nth 0 (ss_mem ssx) ca_out_region) in
        let HRQ := fresh "HRQ" in
        pose proof (st_ok_region_nth (segs := pa_segs) E4 (abs_ss pa_val ssx) _ 0 r0 HS ltac:(vm_compute; reflexivity)) as HRQ;
        cbn [ms_mem restrict] in HRQ;
        assert (HZ : mbyte pa_segs (mrestrict (w_H W) (ms_mem msc)) (out + s3v) = Some (zb 0));
        [ let V := fresh "V" in
          pose proof (field_of_region (segs := pa_segs) E4 _ 34%nat q _ 0 1 0 1 0 1%N (SLit 0) 0 HRQ
            ltac:(rewrite (proj1 HA34 34%nat ltac:(lia)); exact U34) ltac:(left; reflexivity) ltac:(reflexivity)
            ltac:(cbn; lia) ltac:(cbn; lia)) as V;
          pose proof (V 0%nat ltac:(cbn; lia)) as V0; cbn [Z.of_nat] in V0; rewrite !Z.add_0_r in V0; rewrite <- Eq_q, V0; reflexivity
        | ];
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros ?mat';
        rewrite R1f, (ag_reg regs EXT E4 1 1%bv HAE4 eq_refl), Hraw;
        eapply (apost_leaf_app SK pa_segs B LAWS pa_segs_low COPY_ATTR_AK 0 _ G XO OUT STK sp0 FP ly S W0 mem0 md0 own
          lyc Sc W memc mdc k regs (ms_regs msc) (ms_mem msc) _ _ HJ0);
        [ apply (ajournal_gx_materialize pa_segs B LAWS pa_segs_low); exact HJ3
        | lia | rewrite HK; lia | rewrite HK; lia
        | rewrite ?ca_fds_wvb; exact (proj1 FD3)
        | rewrite ?ca_fs_wvb; exact (proj2 FD3)
        | eapply (aregs_preserved_of_st_ok pa_segs _ E4 _ _ regs EXT HS);
          [exact (ag_le 35 32 _ _ ltac:(lia) HAE4) | vm_compute; reflexivity]
        | let x := fresh "x" in let Hx := fresh "Hx" in let Hw := fresh "Hw" in let HnE := fresh "HnE" in
          intros x Hx Hw HnE; rewrite HK in Hw;
          assert (Hno : ~ (out <= x < out + n)) by (intros Hin; exact (HnE (Wr_in x Hin)));
          rewrite (UN8 x Hx ltac:(lia)), (Hfr3 x Hx ltac:(lia) ltac:(rewrite Qsp; lia)); exact (HVM x Hx Hw)
        | intros ?x ?Hp; apply P8; apply Hpres3; apply HPM; assumption
        | intros ?x ?Hx; rewrite HK in *; apply (ca_win G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k HJ3); lia
        | let x := fresh "x" in let Hx := fresh "Hx" in
          intros x (?r & ?Hr & Hx); destruct Hr as [<- | []]; unfold aivl in Hx; cbn [fst snd] in Hx;
          destruct (Z.eqb_spec out 0) as [?|_]; [lia|]; unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia
        | cbv beta; split; [apply set_fs_self|]; split; [apply Permutation_refl|]; split;
          [ intros _ _ l' pay' HU' Hl' HB' Hlen';
            eapply (ca_post_c pa_segs (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem msc)) a out n l pay
              HU ltac:(unfold RTA_HDR; lia) HPAY Hlen Hn1 ltac:(lia) ltac:(lia));
            [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
              apply (lw_mbyte_of_aview pa_segs);
              rewrite (UN8 (out + i) ltac:(lia) ltac:(lia)), (Hcpy i ltac:(lia));
              rewrite (HVM (a + 4 + i) ltac:(lia) ltac:(lia)); f_equal; unfold RTA_HDR; lia
            | rewrite <- Eq_s3; exact HZ
            | exact HU' | exact Hl' | exact HB' | exact Hlen' ]
          | intros _ _; apply (ca_abuf_kept pa_segs (w_H W) memc (ms_mem msc) out n Habuf);
            intros ?x ?Hp; apply P8; apply Hpres3; apply HPM; assumption ] ]
      end.
    * (* j >= n: s3 = n - 1 *)
      rewrite branch_ltu_U, U39, U12 in Hc. apply Z.ltb_ge in Hc.
      assert (Es3 : s3v = n - 1) by lia.
      (* +0x64 .. +0x74: s3 := n - 1, the arguments of checked_memcpy; the call; the alias out + n = q + 1;
         +0x78 .. +0xac *)
      paj_run_tok RUN HS HJ2 SHOK ca_span; [ca_awr Usp2 |];
      let UN7 := fresh "UN7" in let P7 := fresh "P7" in
      pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ regs - 8240 <= x < spZ regs) HFr ltac:(ca_frame_tac)) as UN7;
      pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P7;
      clear HF HFr HG;
      pmkst HS;
      prreg HS (1%bv : bv 5) R1; prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
      prreg HS (10%bv : bv 5) R10; prreg HS (11%bv : bv 5) R11; prreg HS (12%bv : bv 5) R12;
      rewrite (lv_sigma HV); change (link_sigma LS___asan_memcpy) with 0x52d78;
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
        assert (Q3 : getr rg 3 = w64 (as_gp B)) by (rewrite R3, (ag_reg regs EXT E2 3 3%bv HAE2 eq_refl); exact Hgp);
        assert (Q4 : getr rg 4 = w64 (as_tp B)) by (rewrite R4, (ag_reg regs EXT E2 4 4%bv HAE2 eq_refl); exact Htp);
        assert (Qsp : spZ rg = spZ regs - 48)
          by (unfold spZ at 1; rewrite R2, Usp2, unsigned_lit_small by lia; reflexivity);
        assert (Q10 : getr rg 10 = w64 out) by (rewrite R10, (ag_reg regs EXT E2 11 11%bv HAE2 eq_refl); exact G11);
        assert (Q11 : getr rg 11 = w64 (a + 4))
          by (rewrite R11, (ag_reg regs EXT E2 10 10%bv HAE2 eq_refl), G10; unfold w64; rewrite unsigned_lit_small by lia; reflexivity);
        assert (Q12 : getr rg 12 = w64 s3v) by (rewrite R12; (rewrite (ag_reg regs EXT E2 12 12%bv HAE2 eq_refl), G12; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia));
        assert (HVM : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 8240 <= x < spZ regs) ->
          aview pa_segs (w_H W) mm x = aview pa_segs (w_H W) memc x)
          by (intros x Hx Hw; rewrite (UN7 x Hx Hw); exact (UN16 x Hx Hw));
        assert (HPM : forall x, apresent (w_H W) memc x -> apresent (w_H W) mm x)
          by (intros x Hp; exact (P7 x (P16 x Hp)));
        assert (FDy : m_fds mdx = m_fds mdc /\ m_fs mdx = m_fs mdc)
          by (rewrite ?ca_fds_wvb, ?ca_fs_wvb; exact FD2)
      end;
      clear R2 R3 R4 R10 R11 R12 UN7 P7.
      eapply SRr_bind;
      [ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
          eapply (aj_gx_intrin_at SK pa_segs B LAWS pa_segs_low OCpy 0x52d78 AMEMCPY
            G XO OUT W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k out (a + 4) s3v _ HGok HJ2 Q10 Q11 Q12);
          [ lia | lia | lia
          | rewrite Qsp; lia | rewrite Qsp; lia | rewrite Qsp; lia
          | exact Q3 | exact Q4 | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
          | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
            let Haw := fresh "Haw" in let Hxo := fresh "Hxo" in let HGx := fresh "HGx" in let Hox := fresh "Hox" in
            destruct (Hajw x (Wr_in x ltac:(lia))) as [[Haw Hxo] | [HGx | Hox]];
            [ left; split; [exact Haw | split; [exact Hxo | rewrite Qsp; lia]]
            | right; left; split; [exact HGx|];
              apply (writable_kept (segs := pa_segs) (w_H W) memc mm x (HPM x));
              let junk := fresh "junk" in let Hjl := fresh "Hjl" in let Hwr := fresh "Hwr" in
              destruct Habuf as (junk & Hjl & (_ & Hwr)); replace x with (out + (x - out)) by lia; apply Hwr; lia
            | right; right; exact Hox ]
          | unfold amem_range; lia
          | eapply (range_addressable_kept_win _ _ (spZ regs - 8240) (spZ regs));
            [ intros ?s ?Hs ?Hns; apply HVM; assumption | lia | lia | lia
            | exact (ca_ra_sub _ out n out s3v HRAO ltac:(lia) ltac:(lia)) ]
          | intros ?Hpos; eapply (shadow_hull_vis_kept_win _ _ (spZ regs - 8240) (spZ regs));
            [ intros ?s ?Hs ?Hns; apply HVM; assumption | lia | lia | lia | lia
            | exact (ca_hull_sub _ out n s3v HHULLO ltac:(lia)) ]
          | split; [lia|]; split; [lia|]; split;
            [ let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; split; [|rewrite Qsp; lia];
              rewrite (HVM x ltac:(lia) ltac:(lia)); replace x with (a + 4 + (x - (a + 4))) by lia;
              rewrite (HPV (x - (a + 4)) ltac:(lia));
              let Eb := fresh "Eb" in
              destruct (nth_error pay (Z.to_nat (x - (a + 4)))) eqn:Eb;
              [discriminate | apply nth_error_None in Eb; lia]
            |];
            split; [lia|]; split; [unfold amem_range; lia|]; split;
            [ eapply (range_addressable_kept_win _ _ (spZ regs - 8240) (spZ regs));
              [ intros ?s ?Hs ?Hns; apply HVM; assumption | lia | lia | lia
              | exact (ca_ra_sub _ (a + 4) (l - 4) (a + 4) s3v HRAP ltac:(lia) ltac:(lia)) ]
            | intros ?Hpos; eapply (shadow_hull_vis_kept_win _ _ (spZ regs - 8240) (spZ regs));
              [ intros ?s ?Hs ?Hns; apply HVM; assumption | lia | lia | lia | lia
              | exact (ca_hull_sub _ (a + 4) (l - 4) s3v (HHULLP ltac:(lia)) ltac:(lia)) ] ] ]
        end
      | ].
      cbv beta; intros ? ? _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hd3 & Hcpy & Hfr3 & Hpres3 & Hsm3);
      cbv iota in Hcpy;
      assert (FD3 : m_fds md3 = m_fds mdc /\ m_fs md3 = m_fs mdc)
        by (unfold same_but_materialized in Hsm3; rewrite Hsm3;
            rewrite ?ca_fds_wvb, ?ca_fs_wvb; exact FDy);
      clear Hsm3;
      jafter_call_keep_pi HS 51%nat regs3 (mrestrict (w_H W) mem3) HP3 [0]%nat HS3;
      (lazymatch type of HS3 with ?tq -> _ => let HRK := fresh "HRK" in assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end);
      [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
        split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp2; intros ? ?;
        [ apply (lw_mbyte_of_aview pa_segs); apply Hfr3; [lia | lia | rewrite Qsp; lia]
        | intros _; apply (lw_apresent_writable pa_segs);
          apply (ca_win G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k HJ3); lia ]
      | ];
      clear HS; rewrite <- restrict_mkst_fx in HS3; rename HS3 into HS;
      remember (havoc E2 51 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS;
      assert (HEIc3 : img_env pa_val A_LIM E3) by (rewrite HE3; apply img_env_havoc; [assumption | cbv; lia]);
      assert (HA23 : env_agree 51 E2 E3) by (rewrite HE3; apply env_agree_havoc_ge; [lia | apply env_agree_refl]);
      clear HE3;
      assert (HAE3 : env_agree 35 (Ereg regs EXT) E3) by (exact (ag_trans _ _ _ _ HAE2 (ag_le 51 35 _ _ ltac:(lia) HA23)));
      assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite (ag_reg regs EXT E3 2 2%bv HAE3 eq_refl); reflexivity);
      assert (F11 : ew E3 11 = Z_to_bv 64 out) by (rewrite (ag_reg regs EXT E3 11 11%bv HAE3 eq_refl); exact G11);
      assert (F12 : ew E3 12 = Z_to_bv 64 n) by (rewrite (ag_reg regs EXT E3 12 12%bv HAE3 eq_refl); exact G12);
      assert (F39 : ew E3 39 = Z_to_bv 64 j) by (rewrite (proj1 HA23 39%nat ltac:(lia)), H39; exact Hj);
      assert (F34 : ew E3 34 = Z_to_bv 64 q) by (exact (ag_ext regs EXT E3 34 2 HAE3 eq_refl ltac:(lia)));
      assert (F32 : ew E3 32 = Z_to_bv 64 SHADOW_OFF) by (exact (ag_ext regs EXT E3 32 0 HAE3 eq_refl ltac:(lia)));
      assert (U34 : bv_unsigned (ew E3 34) = q) by (rewrite F34; apply unsigned_lit_small; lia);
      let HS5 := fresh "HS5" in
      pose proof (st_ok_pi_add_alias pa_segs pa_val E3 _ _ (SAlu ALU_ADD (SOff 11 0) (SOff 12 0)) (SOff 34 1) HS) as HS5;
      (lazymatch type of HS5 with ?t -> _ => let HR := fresh "HR" in assert (HR : t) by (apply U_inj; rewrite U_SAlu; cbn [zalu_raw];
                  rewrite (U_atom E3 11 out F11 Rout), (U_atom E3 12 n F12 Rn), U_SOff, U34;
                  unfold zcanon, M64; rewrite !Z.mod_small by lia; lia); specialize (HS5 HR); clear HR end);
      clear HS;
      let HS6 := fresh "HS6" in
      pose proof (st_ok_pi_add_fact E3 _ _ 34 (mkAF 1 (2 ^ 47 - 2) 0) HS5) as HS6;
      (lazymatch type of HS6 with ?t -> _ => let HR := fresh "HR" in
         assert (HR : t) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U34, Z.pow_0_r, Z.mod_1_r; lia);
         specialize (HS6 HR); clear HR end);
      clear HS5;
      (lazymatch type of HS6 with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS6 end);
      let HS7 := fresh "HS7" in
      pose proof (st_ok_pi_add_region E3 _ _ ca_out_region HS6 eq_refl) as HS7;
      (lazymatch type of HS7 with ?t -> _ -> _ => let HR := fresh "HR" in assert (HR : t);
         [ refine (ca_region_ok_w1 pa_segs E3 _ 34 q U34 ltac:(lia) ltac:(lia) _);
           cbn [ms_mem restrict mkst];
           replace q with (out + (q - out)) by lia;
           apply (writable_kept (segs := pa_segs) (w_H W) memc mem3 _ (fun Hp => Hpres3 _ (HPM _ Hp)));
           let junk := fresh "junk" in let Hjl := fresh "Hjl" in let Hwr := fresh "Hwr" in
           destruct Habuf as (junk & Hjl & (_ & Hwr)); apply Hwr; lia
         | specialize (HS7 HR); clear HR ] end);
      (lazymatch type of HS7 with ?t -> _ => let HR := fresh "HR" in assert (HR : t);
         [ assert (B34 : base_val E3 (Some 34%nat) = q) by (cbn [base_val]; exact U34);
           assert (B2 : base_val E3 (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp3);
           cbv [ss_mem all_disjoint extent_disjoint ca_out_region YP09.r_base YP09.r_lo YP09.r_hi];
           rewrite B34, B2; split; [lia | exact I]
         | specialize (HS7 HR); clear HR ] end);
      clear HS6; rename HS7 into HS;
      (lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end);
      clear SHOK;
      assert (SHOK3 : sh_ok pa_segs ca_Bx ca_SH1 E3 (mrestrict (w_H W) mem3));
      [ unfold sh_ok, ca_SH1; apply Forall_cons; [|apply Forall_nil];
        unfold shent_ok, app_apart, ca_Bx; cbn [she_m she_lo she_hi];
        rewrite (U_atom E3 32 SHADOW_OFF F32 ltac:(unfold SHADOW_OFF; lia)), (U_atom E3 34 q F34 ltac:(lia)); split;
        [ rewrite Z.add_0_r, Z.sub_0_r; rewrite <- (aview_rd_of pa_segs);
          apply (ra_shadow_eq (aview pa_segs (w_H W) memc));
          [ exact (ca_ra_sub _ out n q 1 HRAO ltac:(lia) ltac:(lia))
          | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
            pose proof (shadow_addr_bounds x ltac:(unfold kHighMemEnd; lia)) as ?Hsb;
            etransitivity;
            [ apply Hfr3; [unfold kHighShadowEnd in *; lia | unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; lia
                          | rewrite Qsp; unfold kHighShadowEnd in *; lia]
            | apply HVM; unfold kHighShadowEnd in *; lia ] ]
        | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia ]
      | ].
      paj_run_tok RUN HS HJ3 SHOK3 ca_span;
      [ repeat (apply awr_ok_x_cons; [let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
          first [lia | rewrite Usp3 in Hx; left; split; [left; lia | lia]
                | rewrite U34 in Hx; exact (Hajw x (Wr_in x ltac:(lia)))] |]);
        apply awr_ok_x_nil
      | ];
      (lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E4 := Ex) in * end);
      assert (HA34 : env_agree 512 E3 E4) by (subst E4; apply ag_ewset2);
      clearbody E4;
      assert (HAE4 : env_agree 35 (Ereg regs EXT) E4) by (exact (ag_trans _ _ _ _ HAE3 (ag_le 512 35 _ _ ltac:(lia) HA34)));
      let UN8 := fresh "UN8" in let P8 := fresh "P8" in
      pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => (spZ regs - 8240 <= x < spZ regs) \/ x = q) HFr
        ltac:(ca_frame_tac)) as UN8;
      pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P8;
      clear HF HFr HG;
      lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
        prreg HS (1%bv : bv 5) R1f;
        let r0 := eval vm_compute in (nth 0 (ss_mem ssx) ca_out_region) in
        let HRQ := fresh "HRQ" in
        pose proof (st_ok_region_nth (segs := pa_segs) E4 (abs_ss pa_val ssx) _ 0 r0 HS ltac:(vm_compute; reflexivity)) as HRQ;
        cbn [ms_mem restrict] in HRQ;
        assert (HZ : mbyte pa_segs (mrestrict (w_H W) (ms_mem msc)) (out + s3v) = Some (zb 0));
        [ let V := fresh "V" in
          pose proof (field_of_region (segs := pa_segs) E4 _ 34%nat q _ 0 1 0 1 0 1%N (SLit 0) 0 HRQ
            ltac:(rewrite (proj1 HA34 34%nat ltac:(lia)); exact U34) ltac:(left; reflexivity) ltac:(reflexivity)
            ltac:(cbn; lia) ltac:(cbn; lia)) as V;
          pose proof (V 0%nat ltac:(cbn; lia)) as V0; cbn [Z.of_nat] in V0; rewrite !Z.add_0_r in V0; rewrite <- Eq_q, V0; reflexivity
        | ];
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros ?mat';
        rewrite R1f, (ag_reg regs EXT E4 1 1%bv HAE4 eq_refl), Hraw;
        eapply (apost_leaf_app SK pa_segs B LAWS pa_segs_low COPY_ATTR_AK 0 _ G XO OUT STK sp0 FP ly S W0 mem0 md0 own
          lyc Sc W memc mdc k regs (ms_regs msc) (ms_mem msc) _ _ HJ0);
        [ apply (ajournal_gx_materialize pa_segs B LAWS pa_segs_low); exact HJ3
        | lia | rewrite HK; lia | rewrite HK; lia
        | rewrite ?ca_fds_wvb; exact (proj1 FD3)
        | rewrite ?ca_fs_wvb; exact (proj2 FD3)
        | eapply (aregs_preserved_of_st_ok pa_segs _ E4 _ _ regs EXT HS);
          [exact (ag_le 35 32 _ _ ltac:(lia) HAE4) | vm_compute; reflexivity]
        | let x := fresh "x" in let Hx := fresh "Hx" in let Hw := fresh "Hw" in let HnE := fresh "HnE" in
          intros x Hx Hw HnE; rewrite HK in Hw;
          assert (Hno : ~ (out <= x < out + n)) by (intros Hin; exact (HnE (Wr_in x Hin)));
          rewrite (UN8 x Hx ltac:(lia)), (Hfr3 x Hx ltac:(lia) ltac:(rewrite Qsp; lia)); exact (HVM x Hx Hw)
        | intros ?x ?Hp; apply P8; apply Hpres3; apply HPM; assumption
        | intros ?x ?Hx; rewrite HK in *; apply (ca_win G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k HJ3); lia
        | let x := fresh "x" in let Hx := fresh "Hx" in
          intros x (?r & ?Hr & Hx); destruct Hr as [<- | []]; unfold aivl in Hx; cbn [fst snd] in Hx;
          destruct (Z.eqb_spec out 0) as [?|_]; [lia|]; unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia
        | cbv beta; split; [apply set_fs_self|]; split; [apply Permutation_refl|]; split;
          [ intros _ _ l' pay' HU' Hl' HB' Hlen';
            eapply (ca_post_c pa_segs (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem msc)) a out n l pay
              HU ltac:(unfold RTA_HDR; lia) HPAY Hlen Hn1 ltac:(lia) ltac:(lia));
            [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
              apply (lw_mbyte_of_aview pa_segs);
              rewrite (UN8 (out + i) ltac:(lia) ltac:(lia)), (Hcpy i ltac:(lia));
              rewrite (HVM (a + 4 + i) ltac:(lia) ltac:(lia)); f_equal; unfold RTA_HDR; lia
            | rewrite <- Eq_s3; exact HZ
            | exact HU' | exact Hl' | exact HB' | exact Hlen' ]
          | intros _ _; apply (ca_abuf_kept pa_segs (w_H W) memc (ms_mem msc) out n Habuf);
            intros ?x ?Hp; apply P8; apply Hpres3; apply HPM; assumption ] ]
      end.
Qed.
End b.
End a.

About copy_attr_aproof.
Print Assumptions copy_attr_aproof.
