(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v; 644 of its 680 lines of code are new or changed and 1269 lines of the source are left out. *)
(* fuzz_close (netlink.h:139-146) on image A (fuzz_link.asan 0x8267c, 80 bytes, 20 instructions; listing
   (internal path) (internal record, sha256 da666a6f173e)): the walk of
   lib/A/Prog/fuzz_close_c.v `fuzz_close_acontract` on link's program tables, through the walk kit lib/A/Prog/LinkWalk.v.

   The code has no frame, no call and no instrumented check (K = 0, EV = 0, SIDE = []): it forms g_nl's address
   with `auipc a1, 0x55a; addi a1, a1, 0x440` (= LA_G_NL, listing slots PHi 6 / PAddHi 6 (A_OBJ 2) 0), then reads
   and writes the four words open / opened / closed / misuse at g_nl + 0x40214 .. +0x40223 with `lui a0, 0x40;
   add a0, a1, a0` and 12-bit offsets. The three paths are
     a0 <> 7                      : misuse := 1, open := 0, closed := closed + 1
     a0 = 7 and open <> 0         : open := 0, closed := closed + 1 (misuse kept)
     a0 = 7 and open = 0          : misuse := 1, open := 0, closed := closed + 1
   and every path returns 0 in a0.

   The symbolic state. ONE region over the base atom A_OBJ 2 (= LA_G_NL), the 16 bytes [NK_OPEN, NK_MISUSE + 4),
   with the four 4-byte fields as chunks over the fresh atoms 32..35 (open, opened, closed, misuse). Its facts
   pin the base atom to LA_G_NL (the run refuses a write window whose base has no range fact: `cells_safe_b` of
   sh_static_ok asks the window to be provably outside the shadow band) and bound the four values from the Pre's
   `nlk_wf` and `nk_closed bs + 1 < 2 ^ 31`, so that the signed 4-byte loads need no sign extension and the
   `addi a1, a1, 1` of the closed counter stays inside 2 ^ 32. There is no shadow entry (SH = []): the
   instrumentation leaves an access at a constant offset into a global unchecked.

   The Post reads the end memory back as one byte list (`abytes_of` of the kit) and reads its fields with
   link_spec.v's `rdn`: the four fields come from the region's chunks after the run (`field_of_region` of
   lib/A/Prog/YC4b.v and the kit's `rdn_of_vals`), every other field is a read of bytes the run did not write
   (the kit's `rdn_agree` over `kept_of_frame`). `nlk_wf` of the end list follows field by field.

   Callee contracts cited: none (fuzz_close calls nothing). Section hypotheses: the image instance
   (PI : PAImg link_listing), its symbol table (HV : LinkVals, discharged by computation at the instance that
   lib/A/Prog/LinkPaCheck.v certifies against the image) and the allocator laws (LAWS : AR_laws pa_segs B,
   the lib/A frame).

   Released proofs (rule 24): none of fuzz_close (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038);
   `proof-index fuzz_close` 0 named, 0 by address, 0 released lemmas, only the delivered package templates and the
   UNRELEASED working-branch contract files; the four-ref grep over origin/main, origin/ossv/recipes,
   origin/ossv/candidates and origin/release/pau-projects-recipes found no released walk).
   Proves function fuzz_close (image A, the asan build). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk fuzz_close_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   The byte algebra of the Post: the end memory's byte list and its fields
   ========================================================================== *)

Section p.
Variable segs : list Segment.

(* a byte of one of the four fields *)
Lemma fc_byte_of : forall (m : word -> option byte) off v j,
  val_mem segs m (LA_G_NL + off) 4 v -> 0 <= j < 4 ->
  exists b, mbyte segs m (LA_G_NL + (off + j)) = Some b.
Proof.
  intros m off v j HV Hj.
  exists (Z_to_bv 8 (le_byte v 4 (Z.to_nat j))).
  replace (LA_G_NL + (off + j)) with (LA_G_NL + off + Z.of_nat (Z.to_nat j)) by lia.
  exact (HV (Z.to_nat j) ltac:(lia)).
Qed.

(* THE POST, from what the run leaves: the four fields and the bytes it did not write. *)
Lemma fc_post : forall (m m2 : word -> option byte) bs mi,
  anlk_at segs m LA_G_NL bs -> nlk_wf bs -> nk_closed bs + 1 < 2 ^ 31 ->
  (forall i, (i < Z.to_nat NK_SIZE)%nat ->
     (Z.of_nat i < NK_OPEN \/ NK_MISUSE + 4 <= Z.of_nat i) ->
     mbyte segs m2 (LA_G_NL + Z.of_nat i) = mbyte segs m (LA_G_NL + Z.of_nat i)) ->
  val_mem segs m2 (LA_G_NL + NK_OPEN) 4 0 ->
  val_mem segs m2 (LA_G_NL + NK_OPENED) 4 (nk_opened bs) ->
  val_mem segs m2 (LA_G_NL + NK_CLOSED) 4 (nk_closed bs + 1) ->
  val_mem segs m2 (LA_G_NL + NK_MISUSE) 4 mi -> 0 <= mi <= 1 ->
  (forall a, 0 <= a < NK_SIZE -> writable_at segs m2 (LA_G_NL + a)) ->
  exists bs', anlk_at segs m2 LA_G_NL bs' /\ nlk_wf bs' /\
    nk_open bs' = 0 /\ nk_opened bs' = nk_opened bs /\ nk_closed bs' = nk_closed bs + 1 /\
    nk_misuse bs' = mi.
Proof.
  intros m m2 bs mi HNLK HWF HCL HOUT V0 V1 V2 V3 Hmi HWR2.
  (* NEVER `cbn` on a goal that holds `rdn bs off n`: it unfolds slice / skipn and reduces Z.to_nat 262680
     to a unary nat (a 30-minute compile, measured). The two powers the bounds need, once: *)
  assert (PW32 : 2 ^ (8 * Z.of_nat 4) = 4294967296) by reflexivity.
  destruct HNLK as ((HAB & HWR) & HLEN).
  assert (HLN : length bs = Z.to_nat NK_SIZE) by (unfold NK_SIZE in *; lia).
  pose proof HAB as (Hg0 & Hgl & Hnth).
  (* every byte of the 271992 is present in m2 *)
  assert (HSOME : forall i, (i < Z.to_nat NK_SIZE)%nat -> exists b, mbyte segs m2 (LA_G_NL + Z.of_nat i) = Some b).
  { intros i Hi.
    destruct (Z_lt_le_dec (Z.of_nat i) NK_OPEN) as [Hlo|Hlo].
    { rewrite (HOUT i Hi ltac:(left; exact Hlo)). rewrite (Hnth i ltac:(lia)).
      destruct (nth_error bs i) as [b|] eqn:Eb; [exists b; reflexivity|].
      exfalso. apply nth_error_None in Eb. lia. }
    destruct (Z_lt_le_dec (Z.of_nat i) (NK_MISUSE + 4)) as [Hhi|Hhi]; swap 1 2.
    { rewrite (HOUT i Hi ltac:(right; exact Hhi)). rewrite (Hnth i ltac:(lia)).
      destruct (nth_error bs i) as [b|] eqn:Eb; [exists b; reflexivity|].
      exfalso. apply nth_error_None in Eb. lia. }
    unfold NK_OPEN, NK_OPENED, NK_CLOSED, NK_MISUSE in *.
    destruct (Z_lt_le_dec (Z.of_nat i) 262680) as [H1|H1].
    { destruct (fc_byte_of m2 NK_OPEN 0 (Z.of_nat i - NK_OPEN) V0 ltac:(unfold NK_OPEN; lia)) as (b & Hb).
      exists b. unfold NK_OPEN in Hb. replace (LA_G_NL + Z.of_nat i) with (LA_G_NL + (262676 + (Z.of_nat i - 262676))) by lia.
      exact Hb. }
    destruct (Z_lt_le_dec (Z.of_nat i) 262684) as [H2|H2].
    { destruct (fc_byte_of m2 NK_OPENED (nk_opened bs) (Z.of_nat i - NK_OPENED) V1 ltac:(unfold NK_OPENED; lia)) as (b & Hb).
      exists b. unfold NK_OPENED in Hb. replace (LA_G_NL + Z.of_nat i) with (LA_G_NL + (262680 + (Z.of_nat i - 262680))) by lia.
      exact Hb. }
    destruct (Z_lt_le_dec (Z.of_nat i) 262688) as [H3|H3].
    { destruct (fc_byte_of m2 NK_CLOSED (nk_closed bs + 1) (Z.of_nat i - NK_CLOSED) V2 ltac:(unfold NK_CLOSED; lia)) as (b & Hb).
      exists b. unfold NK_CLOSED in Hb. replace (LA_G_NL + Z.of_nat i) with (LA_G_NL + (262684 + (Z.of_nat i - 262684))) by lia.
      exact Hb. }
    { destruct (fc_byte_of m2 NK_MISUSE mi (Z.of_nat i - NK_MISUSE) V3 ltac:(unfold NK_MISUSE; lia)) as (b & Hb).
      exists b. unfold NK_MISUSE in Hb. replace (LA_G_NL + Z.of_nat i) with (LA_G_NL + (262688 + (Z.of_nat i - 262688))) by lia.
      exact Hb. } }
  set (bs' := abytes_of segs m2 LA_G_NL (Z.to_nat NK_SIZE)).
  assert (HL' : length bs' = Z.to_nat NK_SIZE) by (unfold bs'; apply abytes_of_length).
  assert (HAB' : abytes segs m2 LA_G_NL bs').
  { unfold bs'. apply abytes_of_abytes; [unfold LA_G_NL; lia | unfold LA_G_NL, NK_SIZE; lia | exact HSOME]. }
  pose proof HAB' as (_ & _ & Hnth').
  (* the bytes outside the four fields are the bytes they were *)
  assert (HN : forall i, (i < Z.to_nat NK_SIZE)%nat ->
    (Z.of_nat i < NK_OPEN \/ NK_MISUSE + 4 <= Z.of_nat i) -> nth_error bs' i = nth_error bs i).
  { intros i Hi Ho. rewrite <- (Hnth' i ltac:(lia)), (HOUT i Hi Ho). exact (Hnth i ltac:(lia)). }
  (* a field read outside the window is the read it was *)
  assert (HR : forall off n, 0 <= off -> 0 <= n -> off + n <= NK_SIZE ->
    (off + n <= NK_OPEN \/ NK_MISUSE + 4 <= off) -> rdn bs' off n = rdn bs off n).
  { intros off n Hoff Hn Hs Ho. apply rdn_agree; [lia | lia | lia | lia |].
    intros kk Hkk. apply HN; [lia|]. destruct Ho; [left; lia | right; lia]. }
  (* the four fields the run wrote *)
  assert (F0 : nk_open bs' = 0).
  { unfold nk_open, fld_u32. change 4 with (Z.of_nat 4).
    apply (rdn_of_vals bs' NK_OPEN 4%nat 0);
      [unfold NK_OPEN; lia | unfold NK_OPEN, NK_SIZE in *; lia | rewrite PW32; lia |].
    (* `apply Hnth'` here would unify `nth_error bs' i` against `mbyte ...` and unfold abytes_of's
       `map _ (seq 0 (Z.to_nat 271992))`: rewrite in the one direction instead. *)
    intros kk Hkk. rewrite <- (Hnth' (Z.to_nat NK_OPEN + kk)%nat ltac:(unfold NK_OPEN, NK_SIZE in *; lia)).
    replace (LA_G_NL + Z.of_nat (Z.to_nat NK_OPEN + kk)) with (LA_G_NL + NK_OPEN + Z.of_nat kk)
      by (unfold NK_OPEN; lia).
    exact (V0 kk Hkk). }
  assert (F1 : nk_opened bs' = nk_opened bs).
  { unfold nk_opened, fld_u32. change 4 with (Z.of_nat 4).
    apply (rdn_of_vals bs' NK_OPENED 4%nat (nk_opened bs));
      [unfold NK_OPENED; lia | unfold NK_OPENED, NK_SIZE in *; lia
       | rewrite PW32; destruct HWF as (_ & _ & _ & _ & _ & Hod & _); lia |].
    (* `apply Hnth'` here would unify `nth_error bs' i` against `mbyte ...` and unfold abytes_of's
       `map _ (seq 0 (Z.to_nat 271992))`: rewrite in the one direction instead. *)
    intros kk Hkk. rewrite <- (Hnth' (Z.to_nat NK_OPENED + kk)%nat ltac:(unfold NK_OPENED, NK_SIZE in *; lia)).
    replace (LA_G_NL + Z.of_nat (Z.to_nat NK_OPENED + kk)) with (LA_G_NL + NK_OPENED + Z.of_nat kk)
      by (unfold NK_OPENED; lia).
    exact (V1 kk Hkk). }
  assert (F2 : nk_closed bs' = nk_closed bs + 1).
  { unfold nk_closed, fld_u32. change 4 with (Z.of_nat 4).
    apply (rdn_of_vals bs' NK_CLOSED 4%nat (nk_closed bs + 1));
      [unfold NK_CLOSED; lia | unfold NK_CLOSED, NK_SIZE in *; lia
       | rewrite PW32; destruct HWF as (_ & _ & _ & _ & _ & _ & Hcl & _); lia |].
    (* `apply Hnth'` here would unify `nth_error bs' i` against `mbyte ...` and unfold abytes_of's
       `map _ (seq 0 (Z.to_nat 271992))`: rewrite in the one direction instead. *)
    intros kk Hkk. rewrite <- (Hnth' (Z.to_nat NK_CLOSED + kk)%nat ltac:(unfold NK_CLOSED, NK_SIZE in *; lia)).
    replace (LA_G_NL + Z.of_nat (Z.to_nat NK_CLOSED + kk)) with (LA_G_NL + NK_CLOSED + Z.of_nat kk)
      by (unfold NK_CLOSED; lia).
    exact (V2 kk Hkk). }
  assert (F3 : nk_misuse bs' = mi).
  { unfold nk_misuse, fld_u32. change 4 with (Z.of_nat 4).
    apply (rdn_of_vals bs' NK_MISUSE 4%nat mi);
      [unfold NK_MISUSE; lia | unfold NK_MISUSE, NK_SIZE in *; lia | rewrite PW32; lia |].
    (* `apply Hnth'` here would unify `nth_error bs' i` against `mbyte ...` and unfold abytes_of's
       `map _ (seq 0 (Z.to_nat 271992))`: rewrite in the one direction instead. *)
    intros kk Hkk. rewrite <- (Hnth' (Z.to_nat NK_MISUSE + kk)%nat ltac:(unfold NK_MISUSE, NK_SIZE in *; lia)).
    replace (LA_G_NL + Z.of_nat (Z.to_nat NK_MISUSE + kk)) with (LA_G_NL + NK_MISUSE + Z.of_nat kk)
      by (unfold NK_MISUSE; lia).
    exact (V3 kk Hkk). }
  exists bs'.
  split.
  { split; [|unfold NK_SIZE in *; lia]. split; [exact HAB'|].
    intros i Hi. replace (LA_G_NL + i) with (LA_G_NL + i) by reflexivity.
    apply HWR2. unfold NK_SIZE in *. lia. }
  split; [|split; [exact F0 | split; [exact F1 | split; [exact F2 | exact F3]]]].
  (* nlk_wf of the end list *)
  pose proof HWF as (Wc & Wn & Ws & Wi & Wo & Wod & Wcl & Wmi & We1 & We2 & We3 & Wl1 & Wl2).
  unfold nlk_wf, nk_n_chunks, nk_next, nk_n_sent, nk_n_if, nk_end_errno, nk_socket_errno, nk_send_errno,
    nk_open, nk_opened, nk_closed, nk_misuse, fld_u32, fld_u64
    in Wc, Wn, Ws, Wi, Wo, Wod, Wcl, Wmi, We1, We2, We3, Wl1, Wl2, HCL |- *.
  rewrite (HR NK_N_CHUNKS 4 ltac:(unfold NK_N_CHUNKS; lia) ltac:(lia)
            ltac:(unfold NK_N_CHUNKS, NK_SIZE; lia) ltac:(left; unfold NK_N_CHUNKS, NK_OPEN; lia)).
  rewrite (HR NK_NEXT 4 ltac:(unfold NK_NEXT; lia) ltac:(lia)
            ltac:(unfold NK_NEXT, NK_SIZE; lia) ltac:(left; unfold NK_NEXT, NK_OPEN; lia)).
  rewrite (HR NK_N_SENT 4 ltac:(unfold NK_N_SENT; lia) ltac:(lia)
            ltac:(unfold NK_N_SENT, NK_SIZE; lia) ltac:(right; unfold NK_N_SENT, NK_MISUSE; lia)).
  rewrite (HR NK_N_IF 4 ltac:(unfold NK_N_IF; lia) ltac:(lia)
            ltac:(unfold NK_N_IF, NK_SIZE; lia) ltac:(right; unfold NK_N_IF, NK_MISUSE; lia)).
  rewrite (HR NK_END_ERRNO 4 ltac:(unfold NK_END_ERRNO; lia) ltac:(lia)
            ltac:(unfold NK_END_ERRNO, NK_SIZE; lia) ltac:(left; unfold NK_END_ERRNO, NK_OPEN; lia)).
  rewrite (HR NK_SOCKET_ERRNO 4 ltac:(unfold NK_SOCKET_ERRNO; lia) ltac:(lia)
            ltac:(unfold NK_SOCKET_ERRNO, NK_SIZE; lia) ltac:(left; unfold NK_SOCKET_ERRNO, NK_OPEN; lia)).
  rewrite (HR NK_SEND_ERRNO 4 ltac:(unfold NK_SEND_ERRNO; lia) ltac:(lia)
            ltac:(unfold NK_SEND_ERRNO, NK_SIZE; lia) ltac:(left; unfold NK_SEND_ERRNO, NK_OPEN; lia)).
  unfold nk_open, nk_opened, nk_closed, nk_misuse, fld_u32 in F0, F1, F2, F3.
  rewrite F0, F1, F2, F3.
  split; [exact Wc|]. split; [exact Wn|]. split; [exact Ws|]. split; [exact Wi|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact We1|]. split; [exact We2|]. split; [exact We3|].
  split.
  - intros i Hi. rewrite (HR (NK_CHUNK_LEN + 8 * i) 8 ltac:(unfold NK_CHUNK_LEN; lia) ltac:(lia)
      ltac:(unfold NK_CHUNK_LEN, NK_SIZE, NL_CHUNKS in *; lia)
      ltac:(left; unfold NK_CHUNK_LEN, NK_OPEN, NL_CHUNKS in *; lia)).
    apply Wl1. lia.
  - intros i Hi. rewrite (HR (NK_SENT_LEN + 8 * i) 8 ltac:(unfold NK_SENT_LEN; lia) ltac:(lia)
      ltac:(unfold NK_SENT_LEN, NK_SIZE, NL_SENT_MAX in *; lia)
      ltac:(right; unfold NK_SENT_LEN, NK_MISUSE; lia)).
    apply Wl2. lia.
Qed.
End p.

(* ==========================================================================
   The walk
   ========================================================================== *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HV : LinkVals.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the four words of g_nl the code reads and writes, over the fresh atoms 32..35 *)
Definition fc_region : YP09.region :=
  YP09.mkRegion (Some 243%nat) 262676 262692 262676 262692   (* 243 = A_OBJ 2, the atom of g_nl *)
    [YP09.mkChunk 262676 (CVal 4 (SOff 32 0)); YP09.mkChunk 262680 (CVal 4 (SOff 33 0));
     YP09.mkChunk 262684 (CVal 4 (SOff 34 0)); YP09.mkChunk 262688 (CVal 4 (SOff 35 0))].
Definition fc_facts : facts :=
  mkFacts [(243%nat, mkAF LA_G_NL LA_G_NL 0); (32%nat, mkAF 0 1 0); (33%nat, mkAF 0 (2 ^ 31 - 1) 0);
           (34%nat, mkAF 0 (2 ^ 31 - 2) 0); (35%nat, mkAF 0 1 0)] [] [].
Definition fc_ss : sstate := mkSS AF_fuzz_close sr_atoms [fc_region] None fc_facts.
Definition fc_Bx : sv := SLit SHADOW_OFF.
Definition fc_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* THE END OF EVERY PATH. The three paths differ only in the misuse word, so they share this step: from the
   journal at the call and at the end, the four field values the run leaves, the bytes it did not write and the
   register result, it gives the whole `apost` of the contract at the return config. *)
Lemma fc_finish : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regs2 : bvmap 5 word) mem2 md2 bs mi,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  sp0 - STK <= spZ regs - FUZZ_CLOSE_AK ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) ->
     aview pa_segs (w_H W) mem2 a = aview pa_segs (w_H W) memc a) ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) ->
  anlk_at pa_segs (rdW W memc) LA_G_NL bs -> nlk_wf bs -> nk_closed bs + 1 < 2 ^ 31 ->
  val_mem pa_segs (rdW W mem2) (LA_G_NL + NK_OPEN) 4 0 ->
  val_mem pa_segs (rdW W mem2) (LA_G_NL + NK_OPENED) 4 (nk_opened bs) ->
  val_mem pa_segs (rdW W mem2) (LA_G_NL + NK_CLOSED) 4 (nk_closed bs + 1) ->
  val_mem pa_segs (rdW W mem2) (LA_G_NL + NK_MISUSE) 4 mi -> 0 <= mi <= 1 ->
  mi = (if (aarg regs 0 =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1) ->
  getr regs2 10 = w64 0 ->
  apost SK pa_segs B FUZZ_CLOSE_AK 0 (fun a => inFP (fuzz_close_awr regs (rdW W memc)) a)
    G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (fun ly2 S2 W2 regs2' mem2' md2' =>
       S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       fuzz_close_apost pa_segs regs (rdW W memc) regs2' (rdW W2 mem2'))
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom pa_segs)) md2).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 bs mi
  HJ HJ2 Hfds Hfs Hlo HP UN HGr HNLK HWF HCL V0 V1 V2 V3 Hmi Hmieq Ha0.
assert (HWIN : FUZZ_CLOSE_AK = 0) by reflexivity.
(* the write set, as a range *)
assert (HE : forall a, inFP (fuzz_close_awr regs (rdW W memc)) a <->
                       LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4).
{ intros a. unfold fuzz_close_awr. split.
  - intros (r & Hin & Hr). cbn [In] in Hin. destruct Hin as [<- | []]. cbn [fst snd] in Hr. exact Hr.
  - intros Hr. exists (LA_G_NL + NK_OPEN, LA_G_NL + NK_MISUSE + 4).
    split; [left; reflexivity | cbn [fst snd]; exact Hr]. }
apply (apost_leaf SK pa_segs B LAWS pa_segs_low FUZZ_CLOSE_AK 0
         (fun a => inFP (fuzz_close_awr regs (rdW W memc)) a)
         G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 _
         HJ HJ2 ltac:(lia) Hlo ltac:(lia) Hfds Hfs HP).
- intros a Ha _ HnE. apply UN; [exact Ha|]. intros Hr. apply HnE. apply HE. exact Hr.
- intros a Hp. exact (apresent_grows (w_H W) memc mem2 a HGr Hp).
- intros a Ha. exfalso. lia.
- intros x Hx. apply HE in Hx. unfold LA_G_NL, NK_OPEN, NK_MISUSE, SHADOW_OFF in *. lia.
- (* Q *)
  split; [symmetry; apply set_fs_self|]. split; [apply Permutation_refl|].
  intros bs0 HNLK0.
  assert (Ebs : bs0 = bs).
  { apply (abytes_unique pa_segs (rdW W memc) LA_G_NL);
      [exact (proj1 (proj1 HNLK0)) | exact (proj1 (proj1 HNLK))
       | destruct HNLK0 as (_ & L0); destruct HNLK as (_ & L1); unfold NK_SIZE in *; lia]. }
  subst bs0.
  assert (HOUTb : forall i, (i < Z.to_nat NK_SIZE)%nat ->
     (Z.of_nat i < NK_OPEN \/ NK_MISUSE + 4 <= Z.of_nat i) ->
     mbyte pa_segs (rdW W mem2) (LA_G_NL + Z.of_nat i) = mbyte pa_segs (rdW W memc) (LA_G_NL + Z.of_nat i)).
  { intros i Hi Ho. apply (mbyte_of_aview pa_segs). apply UN;
      [unfold LA_G_NL, NK_SIZE in *; lia | unfold NK_OPEN, NK_MISUSE in *; destruct Ho; lia]. }
  assert (HWR2 : forall a, 0 <= a < NK_SIZE -> writable_at pa_segs (rdW W mem2) (LA_G_NL + a)).
  { intros a Ha. apply (writable_kept (segs := pa_segs) (w_H W) memc mem2 (LA_G_NL + a)).
    - intros Hp. exact (apresent_grows (w_H W) memc mem2 (LA_G_NL + a) HGr Hp).
    - destruct HNLK as ((_ & HWR) & HLEN). apply HWR. unfold NK_SIZE in *. lia. }
  destruct (fc_post pa_segs (rdW W memc) (rdW W mem2) bs mi HNLK HWF HCL HOUTb V0 V1 V2 V3 Hmi HWR2)
    as (bs' & A1 & A2 & A3 & A4 & A5 & A6).
  exists bs'. split; [exact A1|]. split; [exact A2|]. split; [exact Ha0|].
  split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. rewrite A6. exact Hmieq.
Qed.

(* fuzz_close's walk never reads `arodata_okP`, so the contract holds at EVERY read-only window; the
   cross-lane rule is that a caller meets it at the constants PCAP_RLO / PCAP_RHI of
   lib/A/Prog/PcapRelro.v, which fuzz_close_acontract_pcap below states. *)
Theorem fuzz_close_aproof : forall rlo rhi, fuzz_close_acontract SK pa_segs rlo rhi B.
Proof.
intros rlo rhi.
unfold fuzz_close_acontract, aleaf.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HP.
pose proof HPRE as HPRE0.
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof HJ as HJ0.
destruct HP as (bs & HNLK & HWF & HCL).
pose proof HNLK as HNLK0.
destruct HNLK as ((HAB & HWR) & HLEN).
pose proof HWF as (Wc & Wn & Ws & Wi & Wo & Wod & Wcl & Wmi & We1 & We2 & We3 & Wl1 & Wl2).
assert (HLN : length bs = Z.to_nat NK_SIZE) by (unfold NK_SIZE in *; lia).
assert (HFK : FUZZ_CLOSE_AK = 0) by reflexivity.
assert (PW32N : 2 ^ (8 * Z.of_N 4) = 4294967296) by reflexivity.
(* the four fields at the entry *)
assert (V0 : val_mem pa_segs (rdW W memc) (LA_G_NL + NK_OPEN) 4 (nk_open bs)).
{ unfold nk_open, fld_u32. change 4 with (Z.of_nat 4).
  apply (val_mem_of_abytes pa_segs (rdW W memc) LA_G_NL bs NK_OPEN 4%nat HAB);
    [unfold NK_OPEN; lia | unfold NK_OPEN, NK_SIZE in *; lia]. }
assert (V1 : val_mem pa_segs (rdW W memc) (LA_G_NL + NK_OPENED) 4 (nk_opened bs)).
{ unfold nk_opened, fld_u32. change 4 with (Z.of_nat 4).
  apply (val_mem_of_abytes pa_segs (rdW W memc) LA_G_NL bs NK_OPENED 4%nat HAB);
    [unfold NK_OPENED; lia | unfold NK_OPENED, NK_SIZE in *; lia]. }
assert (V2 : val_mem pa_segs (rdW W memc) (LA_G_NL + NK_CLOSED) 4 (nk_closed bs)).
{ unfold nk_closed, fld_u32. change 4 with (Z.of_nat 4).
  apply (val_mem_of_abytes pa_segs (rdW W memc) LA_G_NL bs NK_CLOSED 4%nat HAB);
    [unfold NK_CLOSED; lia | unfold NK_CLOSED, NK_SIZE in *; lia]. }
assert (V3 : val_mem pa_segs (rdW W memc) (LA_G_NL + NK_MISUSE) 4 (nk_misuse bs)).
{ unfold nk_misuse, fld_u32. change 4 with (Z.of_nat 4).
  apply (val_mem_of_abytes pa_segs (rdW W memc) LA_G_NL bs NK_MISUSE 4%nat HAB);
    [unfold NK_MISUSE; lia | unfold NK_MISUSE, NK_SIZE in *; lia]. }
(* the environment *)
set (EXT := [w64 (nk_open bs); w64 (nk_opened bs); w64 (nk_closed bs); w64 (nk_misuse bs)]).
set (E := Eimg (Ereg regs EXT)).
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs EXT) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1%nat = getr regs 1)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs EXT 1 1%bv eq_refl)).
assert (E10 : ew E 10%nat = getr regs 10)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs EXT 10 10%bv eq_refl)).
assert (E32 : ew E 32%nat = w64 (nk_open bs))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs EXT 0)).
assert (E33 : ew E 33%nat = w64 (nk_opened bs))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs EXT 1)).
assert (E34 : ew E 34%nat = w64 (nk_closed bs))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs EXT 2)).
assert (E35 : ew E 35%nat = w64 (nk_misuse bs))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs EXT 3)).
assert (EOBJ : ew E 243%nat = Z_to_bv 64 LA_G_NL).
{ subst E. change (243%nat) with (A_OBJ 2). rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite (lv_obj HV 2%nat ltac:(unfold link_nobj; lia)). reflexivity. }
assert (UOBJ : bv_unsigned (ew E 243%nat) = LA_G_NL)
  by (rewrite EOBJ; apply unsigned_lit_small; unfold LA_G_NL; lia).
assert (U32 : bv_unsigned (ew E 32%nat) = nk_open bs) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33%nat) = nk_opened bs) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34%nat) = nk_closed bs) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35%nat) = nk_misuse bs) by (rewrite E35; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs EXT) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
(* the entry state *)
assert (HS : st_ok_pi pa_segs pa_val E fc_ss
   (restrict (w_H W) (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_fuzz_close)) memc (seg_rom pa_segs)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold fc_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UOBJ. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split.
    + intros o Ho. cbn [ms_mem restrict mkst]. apply HWR. unfold NK_SIZE in *. lia.
    + repeat (apply Forall_cons); [| | | | apply Forall_nil].
      * apply (chunk_ok_val pa_segs E _ LA_G_NL 262676 4%N (SOff 32 0) (nk_open bs));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | rewrite PW32N; lia | cbv; discriminate | cbn [ms_mem restrict mkst]; exact V0].
      * apply (chunk_ok_val pa_segs E _ LA_G_NL 262680 4%N (SOff 33 0) (nk_opened bs));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | rewrite PW32N; lia | cbv; discriminate | cbn [ms_mem restrict mkst]; exact V1].
      * apply (chunk_ok_val pa_segs E _ LA_G_NL 262684 4%N (SOff 34 0) (nk_closed bs));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | rewrite PW32N; lia | cbv; discriminate | cbn [ms_mem restrict mkst]; exact V2].
      * apply (chunk_ok_val pa_segs E _ LA_G_NL 262688 4%N (SOff 35 0) (nk_misuse bs));
          [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | rewrite PW32N; lia | cbv; discriminate | cbn [ms_mem restrict mkst]; exact V3].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I].
    cbn [fc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UOBJ, U32, U33, U34, U35.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok pa_segs fc_Bx (@nil shent) E (mrestrict (w_H W) memc)) by (apply Forall_nil).
assert (HCFG : cfg_at pa_segs FUZZ_CLOSE_A regs memc mdc
             = mkCfg (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_fuzz_close)) memc (seg_rom pa_segs)) mdc).
{ unfold cfg_at. rewrite (lv_text HV). reflexivity. }
rewrite HCFG.
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (BR := paj_branch (PI := PI)).
pose (RET := paj_ret_at (PL := PL_link) (PI := PI)).
(* the five instructions up to `bne a0, a2` *)
paj_run_tok RUN HS HJ SHOK fc_span.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. unfold fc_region in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite UOBJ in Ha.
  apply (Hajw a). exists (LA_G_NL + NK_OPEN, LA_G_NL + NK_MISUSE + 4).
  split; [left; reflexivity|]. cbn [fst snd]. unfold NK_OPEN, NK_MISUSE in *. lia. }
  lazymatch goal with
  | HFrx : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2) |- _ =>
    assert (UN1 : forall a, 0 <= a < 2 ^ 64 ->
               ~ (LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) ->
               aview pa_segs (w_H Wx) m2 a = aview pa_segs (w_H Wx) m1 a)
      by (apply (kept_of_frame (segs := pa_segs) Ex rsx (w_H Wx) m1 m2
                  (fun a => LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) HFrx);
          intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite UOBJ in Hrr;
                   unfold LA_G_NL, NK_OPEN, NK_MISUSE in *; lia |]);
          destruct Hin);
    clear HFrx
  end.
  lazymatch goal with
  | HGx : mem_grows (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2) |- _ =>
    assert (GR1 : mem_grows (mrestrict (w_H Wx) m1) (mrestrict (w_H Wx) m2)) by exact HGx; clear HGx
  end.
psrr_branch_tok RUN BR HS SHOK fc_span.
- (* a0 <> 7: misuse := 1, open := 0, closed := closed + 1 *)
  assert (Ha0ne : aarg regs 0 <> NL_FD).
  { rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    rewrite (U_atom E 10%nat (aarg regs 0) ltac:(rewrite E10; unfold aarg, argZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
        ltac:(unfold aarg, argZ;
              match goal with |- 0 <= bv_unsigned ?x < _ => pose proof (u64_range x) end; lia)), (U_lit E 7 ltac:(lia)) in Hc.
    unfold NL_FD. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK fc_span.
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. unfold fc_region in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite UOBJ in Ha.
    apply (Hajw a). exists (LA_G_NL + NK_OPEN, LA_G_NL + NK_MISUSE + 4).
    split; [left; reflexivity|]. cbn [fst snd]. unfold NK_OPEN, NK_MISUSE in *. lia. }
  lazymatch goal with
  | HFrx : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2) |- _ =>
    assert (UN2 : forall a, 0 <= a < 2 ^ 64 ->
               ~ (LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) ->
               aview pa_segs (w_H Wx) m2 a = aview pa_segs (w_H Wx) m1 a)
      by (apply (kept_of_frame (segs := pa_segs) Ex rsx (w_H Wx) m1 m2
                  (fun a => LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) HFrx);
          intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite UOBJ in Hrr;
                   unfold LA_G_NL, NK_OPEN, NK_MISUSE in *; lia |]);
          destruct Hin);
    clear HFrx
  end.
  lazymatch goal with
  | HGx : mem_grows (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2) |- _ =>
    assert (GR2 : mem_grows (mrestrict (w_H Wx) m1) (mrestrict (w_H Wx) m2)) by exact HGx; clear HGx
  end.
  lazymatch goal with
  | HSy : st_ok_pi _ _ _ _ (restrict _ ?msy) |- _ =>
    assert (UNa : forall a, 0 <= a < 2 ^ 64 ->
               ~ (LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) ->
               aview pa_segs (w_H W) (ms_mem msy) a = aview pa_segs (w_H W) memc a)
      by (intros a Ha Hn; etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)])
  end.
  lazymatch goal with
  | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) fc_region) in
    pose proof (st_ok_region_nth (segs := pa_segs) E (abs_ss pa_val ssx) (restrict (w_H W) msx) 0%nat r0 HSx
                  ltac:(vm_compute; reflexivity)) as HRg
  end.
  cbn [ms_mem restrict mkst] in HRg.
  pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262676 4%N (SLit 0) 0
                HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P0.
  pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262680 4%N (SOff 33 0) (nk_opened bs)
                HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P1.
  pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262684 4%N (SOff 34 1) (nk_closed bs + 1)
                HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                ltac:(cbn [sv_denot]; rewrite E34; unfold v_addi; rewrite unsigned_lit_small by lia;
                      reflexivity)
                ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P2.
  pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262688 4%N (SLit 1) (1)
                HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                ltac:(reflexivity)
                ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P3.
  cbn [N.to_nat] in P0, P1, P2, P3.
  lazymatch goal with
  | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    prreg HSx (1%bv : bv 5) R1; prreg HSx (10%bv : bv 5) R10;
    eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
    intros mat'
  end.
  rewrite R1, E1. unfold YK0s.ret_ok in Hraw. rewrite Hraw.
  eapply (fc_finish G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ bs (1)
            HJ0).
  + apply ajournal_gx_materialize; first [exact LAWS | exact pa_segs_low | exact HJ].
  + repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  + repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  + exact Hwlo.
  + eapply (aregs_preserved_of_st_ok pa_segs (w_H W) E _ _ regs EXT);
      [eassumption | exact HAE | vm_compute; reflexivity].
  + exact UNa.
  + exact (mem_grows_trans _ _ _ GR1 GR2).
  + exact HNLK0.
  + exact HWF.
  + exact HCL.
  + exact P0.
  + exact P1.
  + exact P2.
  + exact P3.
  + lia.
  + destruct (Z.eqb_spec (aarg regs 0) NL_FD) as [Hq|Hq];
      [exfalso; exact (Ha0ne Hq) | reflexivity].
  + rewrite R10. reflexivity.
- (* a0 = 7: on to `bnez a0` with a0 = open *)
  assert (Ha0eq : aarg regs 0 = NL_FD).
  { rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    rewrite (U_atom E 10%nat (aarg regs 0) ltac:(rewrite E10; unfold aarg, argZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
        ltac:(unfold aarg, argZ;
              match goal with |- 0 <= bv_unsigned ?x < _ => pose proof (u64_range x) end; lia)), (U_lit E 7 ltac:(lia)) in Hc.
    unfold NL_FD. exact Hc. }
  clear Hc.
  (* the load of g_nl.open and the `bnez a0` are a run of their own *)
  paj_run_tok RUN HS HJ SHOK fc_span.
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. unfold fc_region in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite UOBJ in Ha.
    apply (Hajw a). exists (LA_G_NL + NK_OPEN, LA_G_NL + NK_MISUSE + 4).
    split; [left; reflexivity|]. cbn [fst snd]. unfold NK_OPEN, NK_MISUSE in *. lia. }
  lazymatch goal with
  | HFrx : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2) |- _ =>
    assert (UNm : forall a, 0 <= a < 2 ^ 64 ->
               ~ (LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) ->
               aview pa_segs (w_H Wx) m2 a = aview pa_segs (w_H Wx) m1 a)
      by (apply (kept_of_frame (segs := pa_segs) Ex rsx (w_H Wx) m1 m2
                  (fun a => LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) HFrx);
          intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin];
                  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite UOBJ in Hrr;
                   unfold LA_G_NL, NK_OPEN, NK_MISUSE in *; lia |]);
          destruct Hin);
    clear HFrx
  end.
  lazymatch goal with
  | HGx : mem_grows (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2) |- _ =>
    assert (GRm : mem_grows (mrestrict (w_H Wx) m1) (mrestrict (w_H Wx) m2)) by exact HGx; clear HGx
  end.
  (* fold the two steps so far into one, so the sub-leaves compose exactly two *)
  lazymatch goal with
  | HSy : st_ok_pi _ _ _ _ (restrict _ ?msy) |- _ =>
    assert (UN1' : forall a, 0 <= a < 2 ^ 64 ->
               ~ (LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) ->
               aview pa_segs (w_H W) (ms_mem msy) a = aview pa_segs (w_H W) memc a)
      by (intros a Ha Hn; etransitivity; [exact (UNm a Ha Hn) | exact (UN1 a Ha Hn)])
  end.
  assert (GR1' := mem_grows_trans _ _ _ GR1 GRm).
  clear UN1 UNm GR1 GRm. rename UN1' into UN1. rename GR1' into GR1.
  psrr_branch_tok RUN BR HS SHOK fc_span.
  + (* open <> 0: misuse kept *)
    assert (Hopen : nk_open bs <> 0).
    { rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
      rewrite (U_atom E 32%nat (nk_open bs) E32 ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hc. exact Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK fc_span.
    { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      intros a Ha. unfold fc_region in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite UOBJ in Ha.
      apply (Hajw a). exists (LA_G_NL + NK_OPEN, LA_G_NL + NK_MISUSE + 4).
      split; [left; reflexivity|]. cbn [fst snd]. unfold NK_OPEN, NK_MISUSE in *. lia. }
  lazymatch goal with
    | HFrx : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2) |- _ =>
      assert (UN2 : forall a, 0 <= a < 2 ^ 64 ->
                 ~ (LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) ->
                 aview pa_segs (w_H Wx) m2 a = aview pa_segs (w_H Wx) m1 a)
        by (apply (kept_of_frame (segs := pa_segs) Ex rsx (w_H Wx) m1 m2
                    (fun a => LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) HFrx);
            intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin];
                    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite UOBJ in Hrr;
                     unfold LA_G_NL, NK_OPEN, NK_MISUSE in *; lia |]);
            destruct Hin);
      clear HFrx
    end.
  lazymatch goal with
    | HGx : mem_grows (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2) |- _ =>
      assert (GR2 : mem_grows (mrestrict (w_H Wx) m1) (mrestrict (w_H Wx) m2)) by exact HGx; clear HGx
    end.
    lazymatch goal with
    | HSy : st_ok_pi _ _ _ _ (restrict _ ?msy) |- _ =>
      assert (UNa : forall a, 0 <= a < 2 ^ 64 ->
                 ~ (LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) ->
                 aview pa_segs (w_H W) (ms_mem msy) a = aview pa_segs (w_H W) memc a)
        by (intros a Ha Hn; etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)])
    end.
  lazymatch goal with
    | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) fc_region) in
      pose proof (st_ok_region_nth (segs := pa_segs) E (abs_ss pa_val ssx) (restrict (w_H W) msx) 0%nat r0 HSx
                    ltac:(vm_compute; reflexivity)) as HRg
    end.
    cbn [ms_mem restrict mkst] in HRg.
    pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262676 4%N (SLit 0) 0
                  HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                  ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P0.
    pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262680 4%N (SOff 33 0) (nk_opened bs)
                  HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                  ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                  ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P1.
    pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262684 4%N (SOff 34 1) (nk_closed bs + 1)
                  HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                  ltac:(cbn [sv_denot]; rewrite E34; unfold v_addi; rewrite unsigned_lit_small by lia;
                        reflexivity)
                  ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P2.
    pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262688 4%N (SOff 35 0) (nk_misuse bs)
                  HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                  ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                  ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P3.
    cbn [N.to_nat] in P0, P1, P2, P3.
    lazymatch goal with
    | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      prreg HSx (1%bv : bv 5) R1; prreg HSx (10%bv : bv 5) R10;
      eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
      intros mat'
    end.
    rewrite R1, E1. unfold YK0s.ret_ok in Hraw. rewrite Hraw.
    eapply (fc_finish G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ bs (nk_misuse bs)
              HJ0).
    * apply ajournal_gx_materialize; first [exact LAWS | exact pa_segs_low | exact HJ].
    * repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    * repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    * exact Hwlo.
    * eapply (aregs_preserved_of_st_ok pa_segs (w_H W) E _ _ regs EXT);
        [eassumption | exact HAE | vm_compute; reflexivity].
    * exact UNa.
    * exact (mem_grows_trans _ _ _ GR1 GR2).
    * exact HNLK0.
    * exact HWF.
    * exact HCL.
    * exact P0.
    * exact P1.
    * exact P2.
    * exact P3.
    * lia.
    * rewrite Ha0eq, Z.eqb_refl. cbn [andb].
      destruct (Z.eqb_spec (nk_open bs) 0) as [Hz|Hz]; [exfalso; exact (Hopen Hz) | reflexivity].
    * rewrite R10. reflexivity.
  + (* open = 0: misuse := 1 *)
    assert (Hopen : nk_open bs = 0).
    { rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
      rewrite (U_atom E 32%nat (nk_open bs) E32 ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hc. exact Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK fc_span.
    { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      intros a Ha. unfold fc_region in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite UOBJ in Ha.
      apply (Hajw a). exists (LA_G_NL + NK_OPEN, LA_G_NL + NK_MISUSE + 4).
      split; [left; reflexivity|]. cbn [fst snd]. unfold NK_OPEN, NK_MISUSE in *. lia. }
  lazymatch goal with
    | HFrx : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2) |- _ =>
      assert (UN2 : forall a, 0 <= a < 2 ^ 64 ->
                 ~ (LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) ->
                 aview pa_segs (w_H Wx) m2 a = aview pa_segs (w_H Wx) m1 a)
        by (apply (kept_of_frame (segs := pa_segs) Ex rsx (w_H Wx) m1 m2
                    (fun a => LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) HFrx);
            intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq | Hin];
                    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite UOBJ in Hrr;
                     unfold LA_G_NL, NK_OPEN, NK_MISUSE in *; lia |]);
            destruct Hin);
      clear HFrx
    end.
  lazymatch goal with
    | HGx : mem_grows (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2) |- _ =>
      assert (GR2 : mem_grows (mrestrict (w_H Wx) m1) (mrestrict (w_H Wx) m2)) by exact HGx; clear HGx
    end.
    lazymatch goal with
    | HSy : st_ok_pi _ _ _ _ (restrict _ ?msy) |- _ =>
      assert (UNa : forall a, 0 <= a < 2 ^ 64 ->
                 ~ (LA_G_NL + NK_OPEN <= a < LA_G_NL + NK_MISUSE + 4) ->
                 aview pa_segs (w_H W) (ms_mem msy) a = aview pa_segs (w_H W) memc a)
        by (intros a Ha Hn; etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)])
    end.
  lazymatch goal with
    | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) fc_region) in
      pose proof (st_ok_region_nth (segs := pa_segs) E (abs_ss pa_val ssx) (restrict (w_H W) msx) 0%nat r0 HSx
                    ltac:(vm_compute; reflexivity)) as HRg
    end.
    cbn [ms_mem restrict mkst] in HRg.
    pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262676 4%N (SLit 0) 0
                  HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                  ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P0.
    pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262680 4%N (SOff 33 0) (nk_opened bs)
                  HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                  ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                  ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P1.
    pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262684 4%N (SOff 34 1) (nk_closed bs + 1)
                  HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                  ltac:(cbn [sv_denot]; rewrite E34; unfold v_addi; rewrite unsigned_lit_small by lia;
                        reflexivity)
                  ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P2.
    pose proof (field_of_region E _ 243%nat LA_G_NL _ _ _ _ _ 262688 4%N (SLit 1) (1)
                  HRg UOBJ ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
                  ltac:(reflexivity)
                  ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as P3.
    cbn [N.to_nat] in P0, P1, P2, P3.
    lazymatch goal with
    | HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      prreg HSx (1%bv : bv 5) R1; prreg HSx (10%bv : bv 5) R10;
      eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
      intros mat'
    end.
    rewrite R1, E1. unfold YK0s.ret_ok in Hraw. rewrite Hraw.
    eapply (fc_finish G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ bs (1)
              HJ0).
    * apply ajournal_gx_materialize; first [exact LAWS | exact pa_segs_low | exact HJ].
    * repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    * repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    * exact Hwlo.
    * eapply (aregs_preserved_of_st_ok pa_segs (w_H W) E _ _ regs EXT);
        [eassumption | exact HAE | vm_compute; reflexivity].
    * exact UNa.
    * exact (mem_grows_trans _ _ _ GR1 GR2).
    * exact HNLK0.
    * exact HWF.
    * exact HCL.
    * exact P0.
    * exact P1.
    * exact P2.
    * exact P3.
    * lia.
    * rewrite Hopen. cbn [Z.eqb negb andb]. destruct ((aarg regs 0 =? NL_FD)); reflexivity.
    * rewrite R10. reflexivity.
Qed.

(* at the window the frame's `in_ro` uses (lib/A/ACeg.v:62), the form every caller takes *)
Corollary fuzz_close_aproof_pcap : fuzz_close_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof. exact (fuzz_close_aproof PCAP_RLO PCAP_RHI). Qed.
End b.
End a.
