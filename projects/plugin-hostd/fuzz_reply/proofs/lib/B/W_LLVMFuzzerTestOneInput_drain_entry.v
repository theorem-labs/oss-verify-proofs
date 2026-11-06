(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain of the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of
   fuzz_reply's LLVMFuzzerTestOneInput, its FIRST stage: from the arm's entry 0x8489c through the relay_source call
   to the latch 0x84804 (both skip paths) or to the `jal pthread_mutex_lock` at 0x84900 (the state DLK of
   lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v).  Proves no function (kind: segment walk): relay_source is the cut's
   named contract RSRC (lib/B/W_LLVMFuzzerTestOneInput_cut.v :884), declared below verbatim.

   Read from B's own disassembly (the pinned objdump, sha256 17f5c434bf5755fb...):
     0x8489c  beqz s5,850fc            TRAP NONNULL  (runner: atom 21's lo = 4096, seat R1)
     0x848a0  andi a0,s5,7
     0x848a4  bnez a0,850fc            TRAP ALIGN8   (runner: atom 21's al2 = 3, seat R1)
     0x848a8  sd t1,144(s1)            in.n left -> F+144 (t1 = reg 6 = c_n - k')
     0x848ac  srli a1,s5,0x3 ; add a1,a1,s11 ; lb a1,0(a1)
     0x848b8  bnez a1,84dec            the shadow of s->fd: decided by the shadow entry mkSHE 21 0 96 (g_s is in a
                                       zero-shadow range, dre_HZS)
     0x848bc  lw a0,0(s5)              a0 = s->fd (atom 32)
     0x848c0  jal 85d28 <relay_source> CALL: RSRC, its aleafx_post composed into the arm's journal
     0x848c4  sd zero,192(s1)          at := 0 (F+192)
     0x848c8  beqz a0,84804            no entry for that fd -> the latch
     0x848cc  mv s6,a0
     0x848d0  andi a0,a0,7
     0x848d4  bnez a0,850fc            TRAP ALIGN8   (runner: atom 10's al2 = 3, seat R1; T + 56 j is 8-aligned)
     0x848d8  addi a0,s6,4 ; srli a1,a0,0x3 ; add a1,a1,s11 ; lb a1,0(a1)
     0x848e8  bnez a1,84e14            the shadow of r->eof: decided by mkSHE 10 0 56 (inside the table's block)
     0x848ec  lw a0,0(a0)              a0 = r->eof (atom 32)
     0x848f0  bnez a0,84804            end of file -> the latch
     0x848f4  auipc a0,0x554 ; addi s7,a0,1868 ; mv a0,s7 ; jal 98dbc <pthread_mutex_lock>   ra = 0x84904
   The walk splits on RSRC's two answers before it re-enters the engine at 0x848c4.  With a0 = 0 the seat has only
   the at cell; the run stops at `beqz a0` (not a trap), the walk splits it and refutes the fall-through edge from
   a0 = 0 (lib/B/W_traps.v trap_br_eq, the kit's `beq` value lemma, on this non-trap branch).  With a0 = T + 56 j
   it seats atom 10 with R1's fact, the r->eof field and its shadow entry;
   the runner takes the fall-through of `beqz a0` and of the ALIGN8 trap edge, and the walk splits `bnez a0` (eof).
   Trap table of this stage (each trap edge decided by the runner from the seat, no W_traps.v lemma cited):
     0x8489c NONNULL (atom 21, lo 4096), 0x848a4 ALIGN8 (atom 21, al2 3), 0x848d4 ALIGN8 (atom 10, al2 3). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
(* the kit's branch-value lemmas, cited by qualified name (trap_br_eq on the non-trap `beqz a0` at 0x848c8) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the cut's own Local Notation (lib/B/W_LLVMFuzzerTestOneInput_cut.v:161), which does not leave its file *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ the bytes of the relay's table (pure) *)
(* With 4-byte paddings a source_t is 56 bytes (image A's entry_bytes_length). *)
Lemma de_entry_bytes_length : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes.
  rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.
Lemma de_concat_entry_length : forall es,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  induction es as [|e es IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat length]. rewrite length_app, de_entry_bytes_length, IH by assumption. lia.
Qed.
(* byte k of entry i of the table is byte k of that entry *)
Lemma de_concat_entry_nth : forall es i k d,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (i < length es)%nat -> (k < 56)%nat ->
  nth (56 * i + k) (concat (map entry_bytes es)) d = nth k (entry_bytes (nth i es dr_e0)) d.
Proof.
  induction es as [|e es IH]; intros i k d HF Hi Hk; cbn [length] in Hi; [lia|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat]. destruct i as [|i].
  - replace (56 * 0 + k)%nat with k by lia. cbn [nth].
    apply app_nth1. rewrite de_entry_bytes_length by assumption. exact Hk.
  - rewrite app_nth2 by (rewrite de_entry_bytes_length by assumption; lia).
    rewrite de_entry_bytes_length by assumption.
    replace (56 * S i + k - 56)%nat with (56 * i + k)%nat by lia.
    cbn [nth]. apply IH; [exact HF | lia | exact Hk].
Qed.
Lemma de_nth_Z_to_le_bytes : forall n z k d, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k d Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
(* byte k of the 4-byte little-endian store of v, as val_mem reads it *)
Lemma de_le4_le_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) (Z_to_bv 8 0)) = YO0f.le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold Mem.le4. rewrite de_nth_Z_to_le_bytes by exact Hk.
  rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 v) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by exact Hv. reflexivity.
Qed.
Lemma de_le_byte_1_byte : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by exact Hr. reflexivity.
Qed.
Lemma de_nth_bzs : forall l n, nth n (bzs l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  unfold bzs. induction l as [|b l IH]; intros [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.
(* g_s[i]: in the image, 8-aligned (B's g_s is 0x5d8e60 = 766412 * 8; image A's witness does not apply) *)
Lemma de_slot : forall i, (i < 4)%nat ->
  4096 <= rg_s fr_RG + ASRC * Z.of_nat i /\ rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= rg_s fr_RG + 4 * ASRC /\
  (rg_s fr_RG + ASRC * Z.of_nat i) mod 8 = 0 /\ rg_s fr_RG + 4 * ASRC <= 0x5d8fe0.
Proof.
  intros i Hi. assert (HRS : rg_s fr_RG = 0x5d8e60) by reflexivity. assert (HAS : ASRC = 96) by reflexivity.
  rewrite HRS, HAS. split; [lia|]. split; [lia|]. split; [|lia].
  replace (0x5d8e60 + 96 * Z.of_nat i) with ((766412 + 12 * Z.of_nat i) * 8) by lia. apply Z_mod_mult.
Qed.
Section dr.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable MMAX : Z.
Variable EV : dr_env B MT G_fr LS RINV MMAX.
(* the cut's relay_source contract (lib/B/W_LLVMFuzzerTestOneInput_cut.v:884-894), verbatim *)
Hypothesis RSRC : forall W ly S (regs : bvmap 5 word) mem md ch T es fd,
  afn_pre segs B RSRC_STK ly S W regs mem md ch ->
  getr regs 10 = w64 fd -> 0 <= fd < 2 ^ 32 ->
  arelay_at B fr_RG ly S W mem T es -> rom_view segs W mem ->
  SRr segs W (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md)
    (aleafx_post B RSRC_STK regs ly S W mem md
      (fun a0 =>
         (exists j e, nth_error es j = Some e /\ re_fd e = fd /\
            (forall i e', (i < j)%nat -> nth_error es i = Some e' -> re_fd e' <> fd) /\
            a0 = w64 (T + AENT * Z.of_nat j)) \/
         ((forall e, In e es -> re_fd e <> fd) /\ a0 = w64 0))).

(* ------------------------------------------------------------------ the transport kit (lib/B's SEG_LATCH twin,
   a working branch ee519e5e2f5 Section kit / Section w, lt_ -> de_): every fact lcut states of memory
   outside the function's own frame lies below alloc_ceiling + 8 *)
Definition DE_CEIL8 : Z := alloc_ceiling + 8.
Definition de_fp_low (fp : list (Z * Z)) : Prop := Forall (fun r => 0 <= fst r /\ snd r <= DE_CEIL8) fp.
Lemma de_ceil : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. exact (proj1 alloc_ceiling_val). Qed.
Lemma de_ceil_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof. exact (proj1 de_ceil). Qed.
Lemma de_ceil_hi : DE_CEIL8 < 2 ^ 64.
Proof. unfold DE_CEIL8. pose proof de_ceil. lia. Qed.
Ltac de_low :=
  cbn [fst snd gfp]; unfold DE_CEIL8, fr_RG in *;
  cbn [fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof de_ceil_lo; lia.
Lemma de_fp_low_nil : de_fp_low []. Proof. constructor. Qed.
Lemma de_fp_low_cons : forall r fp, 0 <= fst r -> snd r <= DE_CEIL8 -> de_fp_low fp -> de_fp_low (r :: fp).
Proof. intros r fp H1 H2 H3. constructor; [split; assumption | exact H3]. Qed.
Lemma de_fp_low_app : forall f1 f2, de_fp_low f1 -> de_fp_low f2 -> de_fp_low (f1 ++ f2).
Proof. intros f1 f2 H1 H2. apply Forall_app. split; assumption. Qed.
Lemma de_fp_low_forall : forall fp, de_fp_low fp <-> (forall r, In r fp -> 0 <= fst r /\ snd r <= DE_CEIL8).
Proof. intros fp. unfold de_fp_low. apply Forall_forall. Qed.
Lemma de_akept_of_low : forall (W : world segs) mem (W' : world segs) mem' fp,
  (forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a) -> de_fp_low fp -> akept W mem W' mem' fp.
Proof.
  intros W mem W' mem' fp HK Hl r Hr a Ha. rewrite de_fp_low_forall in Hl.
  destruct (Hl r Hr) as [H1 H2]. apply HK. lia.
Qed.
Lemma de_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
Lemma de_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma de_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  assert (Hx : length (text_rec r) = 16%nat) by (unfold text_rec; rewrite length_app; reflexivity).
  cbn [map concat]. rewrite length_app, Hx, IH. cbn [length]. lia.
Qed.
Lemma de_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.
Lemma de_alist : forall ly S (W : world segs) mem md LA l lines,
  AR segs B ly S W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= DE_CEIL8 ->
  de_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : de_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite de_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (de_blk ly S W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite de_bzs_len, length_app. cbn [length].
      unfold DE_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply de_fp_low_cons; [cbn; lia | cbn; lia|]. apply de_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply de_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (de_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply de_fp_low_cons; [cbn; lia | | apply de_fp_low_nil].
    cbn [gfp fst snd]. rewrite de_bzs_len, length_app, de_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold DE_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.
Lemma de_asrc : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= DE_CEIL8 ->
  de_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (de_alist ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (de_alist ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (de_alist ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (de_blk ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply de_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply de_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite de_bzs_len, Hpj. unfold APARTIAL, DE_CEIL8 in *. lia.
    + apply de_fp_low_app; [exact A1|]. apply de_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.
Lemma de_aentry : forall ly S (W : world segs) mem md e,
  AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  de_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : de_fp_low (map (fun k => gfp (gestures_end_b_c.key_addr k)
                                 (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (gestures_end_b_c.key_addr k,
                                                 Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite de_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (de_blk ly S W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite de_bzs_len, length_app. cbn [length].
      unfold DE_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply de_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply de_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (de_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply de_fp_low_cons; [cbn; lia | | apply de_fp_low_nil].
      cbn [gfp snd]. rewrite de_bzs_len, length_app. unfold DE_CEIL8 in *. lia.
    + apply de_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (de_blk ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite de_bzs_len, de_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold DE_CEIL8. pose proof de_ceil_lo. lia. }
        destruct (de_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold DE_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
Lemma de_arelay : forall ly S (W : world segs) mem md G es,
  AR segs B ly S W mem md -> arelay_at B fr_RG ly S W mem G es ->
  de_fp_low (arelay_fp fr_RG G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (de_blk ly S W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : de_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite de_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (de_aentry ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite de_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (de_aentry ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply de_fp_low_cons; [de_low | de_low|].
    apply de_fp_low_cons; [de_low | de_low|].
    apply de_fp_low_cons; [de_low | de_low|].
    apply de_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, DE_CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.
Lemma de_aout : forall ly S (W : world segs) mem md c O mx no cap out,
  AR segs B ly S W mem md -> aout_at B fr_RG ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= DE_CEIL8 ->
  de_fp_low (aout_fp B fr_RG cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply de_fp_low_cons; [de_low | de_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply de_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (de_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply de_fp_low_cons; [cbn; lia | cbn; unfold DE_CEIL8 in *; lia | apply de_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
Lemma de_akept_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= DE_CEIL8 ->
  akept W mem W' mem' [(lo, hi)].
Proof.
  intros W W' mem mem' lo hi HK H1 H2. apply de_akept_of_low; [exact HK|].
  apply de_fp_low_cons; [cbn; lia | cbn; lia | apply de_fp_low_nil].
Qed.
Lemma de_akept_of_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= DE_CEIL8 ->
  forall x, lo <= x < hi -> abyte_kept W mem W' mem' x.
Proof. intros W W' mem mem' lo hi HK H1 H2 x Hx. apply HK. lia. Qed.

(* the errno cell's place (the allocator instance's api_env, dre_TL) *)
Lemma de_errno : 0 <= as_errno B /\ as_errno B + 4 <= DE_CEIL8.
Proof.
  pose proof (pal_env B (dre_TL _ _ _ _ _ _ EV)) as ((HE0 & HE1) & _).
  pose proof de_ceil_lo. unfold DE_CEIL8, kLowMemEnd in *. lia.
Qed.

(* ---- the model ---- *)
Lemma de_amodel_kept : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR segs B ly S W mem md -> amodel_at B ly S W mem m ->
  (forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) KEEP.
  destruct de_errno as [HE0 HE1].
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= DE_CEIL8)
      by (unfold fr_RG, DE_CEIL8; cbn; unfold ASRC; pose proof de_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (de_asrc ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (de_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (de_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (de_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (de_arelay ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3
             (de_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (de_aout ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_RG ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (de_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5).
    apply de_akept_rng; [exact KEEP | cbn; lia | unfold DE_CEIL8; cbn; pose proof de_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6).
    apply de_akept_rng; [exact KEEP | cbn; lia | unfold DE_CEIL8; cbn; pose proof de_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    apply de_akept_rng; [exact KEEP | cbn; lia | unfold DE_CEIL8; cbn; pose proof de_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, DE_CEIL8 in *. pose proof de_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, DE_CEIL8 in *. pose proof de_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, DE_CEIL8 in *. pose proof de_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, DE_CEIL8 in *. pose proof de_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, DE_CEIL8 in *. pose proof de_ceil_lo. lia.
Qed.

(* ---- the frame, the fake frame and its shadow ---- *)
Lemma de_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
(* the three windows this stage writes: relay_source's frame [F - 16, F), in.n's cell [F+144, F+152) and at's
   cell [F+192, F+200); none is a cell of B's aframe_at (F+32 .. F+184, the saved registers at sp0 - 104 ..) *)
Definition de_out (cx : lfcx) (a : Z) : Prop :=
  ~ (lf_F cx - 16 <= a < lf_F cx) /\ ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) /\
  ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8).
Ltac de_outt := unfold de_out, DR_N, DR_AT; repeat split; lia.
Lemma de_aframe_kept : forall cx FF (W W' : world segs) mem mem',
  aframe_at cx FF W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W' mem' a) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a -> writable_at segs (arm W' mem') a) ->
  DE_CEIL8 <= lf_F cx - 16 -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= DE_CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= DE_CEIL8 ->
  aframe_at cx FF W' mem'.
Proof.
  intros cx FF W W' mem mem'
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20
     & A21)
    HK WK HLO HF1 HF2 HFF0 HFF1 HS0 HS1.
  pose proof de_ceil_hi as HC64. pose proof de_ceil_lo as HCL.
  assert (HFpos : 0 <= lf_F cx) by lia.
  assert (KL : forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply HK; [lia | de_outt]).
  split.
  { intros o r Hin. apply (de_sv8_kept W W' mem mem'); [|exact (A1 o r Hin)].
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    intros x Hx. apply HK; [lia | de_outt]. }
  split.
  { intros i Hi. apply WK; [lia | exact (A2 i Hi)]. }
  do 14 (split; [apply (de_sv8_kept W W' mem mem'); [intros x Hx; apply HK; [lia | de_outt] | assumption]|]).
  split; [apply (de_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | exact A17]|].
  split; [apply (de_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | exact A18]|].
  split; [apply (de_sv8_kept W W' mem mem'); [intros x Hx; apply KL; lia | exact A19]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact A20]|].
  split.
  { apply (akept_garr8 W mem); [|exact (proj1 A21)]. intros x Hx.
    unfold fake_shadow in Hx. cbn [length] in Hx. apply KL. lia. }
  apply (akept_awr W mem); [intros x Hx; apply KL; lia | exact (proj2 A21)].
Qed.
(* ---- the input block, the read-only image, the jump table ---- *)
Lemma de_ainput_kept : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR segs B ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (de_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold DE_CEIL8. lia.
Qed.
Lemma de_rom_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> (forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a) ->
  rom_view segs W' mem'.
Proof.
  intros W W' mem mem' HR KEEP a Ha. rewrite <- (HR a Ha).
  assert (Hin : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
  pose proof (pa_segs_low a Hin) as Hlow. pose proof de_ceil_lo.
  exact (proj1 (KEEP a ltac:(unfold DE_CEIL8, kLowMemEnd in *; lia))).
Qed.
Lemma de_jt_kept : forall (W W' : world segs) mem mem',
  jt_rom W mem -> (forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a) -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HJ KEEP i Hi. apply (akept_vm W mem); [|exact (HJ i Hi)].
  intros x Hx. apply KEEP. unfold fr_jtab, DE_CEIL8 in *. pose proof de_ceil_lo. cbn in Hx. lia.
Qed.

(* ---- the numbers of this call's frame, from the entry's contract ---- *)
Lemma de_spF : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320 /\ lf_F cx mod 32 = 0 /\
  Z.of_nat (length (c_pl cx)) = c_n cx /\ 0 <= c_n cx < 2 ^ 26.
Proof.
  intros cx (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold YCfn.LLVMF_STK in Hslo.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hm.
  split; [lia|]. split; [unfold lf_F; lia|].
  split; [unfold lf_F; rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity|].
  split; [lia|]. destruct Hnrng as [(Hz & _) | (Hz & _)]; lia.
Qed.
(* the walk's own fake frame is a live frame of its journal *)
Lemma de_fin : forall cx fpos ly S (W : world segs) mem md k,
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k ->
  In (1, fpos) (frames S).
Proof.
  intros cx fpos ly S W mem md k HJ.
  pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
  rewrite Hfrs. left. reflexivity.
Qed.

(* ---- everything lcut states of memory, as one bundle, and its transport across a run or a call that keeps every
   byte outside this stage's three windows ---- *)
Definition de_ctx (cx : lfcx) (m : lmod) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
  (mem : word -> option byte) : Prop :=
  aframe_at cx (frame_addr ly 1 fpos) W mem /\ sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  amodel_at B ly S W mem m /\ ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem.
Lemma de_ctx_kept : forall cx m fpos ly S (W W' : world segs) mem mem' md,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  AR segs B ly S W mem md -> In (1, fpos) (frames S) ->
  (forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W' mem' a) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a -> writable_at segs (arm W' mem') a) ->
  de_ctx cx m fpos ly S W mem -> de_ctx cx m fpos ly S W' mem'.
Proof.
  intros cx m fpos ly S W W' mem mem' md HB HAR Hfin HK WK (HFR & HFL & HMOD & HIN & HRV & HJT).
  destruct (de_spF cx HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil_lo as HCL. pose proof de_ceil_hi as HC64.
  destruct (frames_bounds segs B LAWS ly S W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly 1 fpos / 8 /\ 8 * (frame_addr ly 1 fpos / 8) <= frame_addr ly 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < DE_CEIL8 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply HK; [lia | unfold DE_CEIL8 in *; de_outt]).
  split; [apply (de_aframe_kept cx _ W W' mem mem' HFR HK WK); unfold DE_CEIL8, SB in *; lia|].
  split; [apply (de_sv8_kept W W' mem mem'); [intros x Hx; apply KL; unfold DE_CEIL8 in *; lia | exact HFL]|].
  split; [exact (de_amodel_kept ly S W mem md W' mem' m HAR HMOD KL)|].
  split; [exact (de_ainput_kept cx ly S W mem md W' mem' HAR HIN Hlen KL)|].
  split; [exact (de_rom_kept W W' mem mem' HRV KL)|].
  exact (de_jt_kept W W' mem mem' HJT KL).
Qed.
(* the registers every state of this stage keeps: lregs_common, s9 = t, s4 = the new cursor, s5 = the source *)
Definition de_regs (cx : lfcx) (t : Z) (m : lmod) (si : nat) (FF : Z) (regs : bvmap 5 word) : Prop :=
  lregs_common B cx FF regs /\ getr regs 25 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 20 = w64 (c_p cx + dr_k' cx m) /\ getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si).
Definition DE_KR : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%bv.
(* the registers the lock path keeps up to the call: DE_KR without s7 (it takes &g_lock at 0x848f8) *)
Definition DE_KD : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%bv.
Ltac de_in := cbn [In jt_kept DE_KR DE_KD]; repeat (first [left; reflexivity | right]).
Lemma de_regs_kept : forall cx t m si FF (regs regs' : bvmap 5 word),
  (forall r, In r DE_KR -> getr regs' r = getr regs r) ->
  de_regs cx t m si FF regs -> de_regs cx t m si FF regs'.
Proof.
  intros cx t m si FF regs regs' HK ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  unfold de_regs, lregs_common.
  rewrite (HK 2%bv ltac:(de_in)), (HK 8%bv ltac:(de_in)), (HK 9%bv ltac:(de_in)), (HK 18%bv ltac:(de_in)),
    (HK 19%bv ltac:(de_in)), (HK 23%bv ltac:(de_in)), (HK 24%bv ltac:(de_in)), (HK 26%bv ltac:(de_in)),
    (HK 27%bv ltac:(de_in)), (HK 3%bv ltac:(de_in)), (HK 4%bv ltac:(de_in)), (HK 25%bv ltac:(de_in)),
    (HK 20%bv ltac:(de_in)), (HK 21%bv ltac:(de_in)).
  repeat split; first [assumption | lia].
Qed.
(* a callee-saved register across a call (lib/B SEG_LATCH's lt_pres) *)
Lemma de_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac de_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Lemma de_regs_pres : forall cx t m si FF (regs regs' : bvmap 5 word),
  aregs_preserved regs regs' -> de_regs cx t m si FF regs -> de_regs cx t m si FF regs'.
Proof.
  intros cx t m si FF regs regs' HP HR. apply (de_regs_kept cx t m si FF regs regs'); [|exact HR].
  intros r Hr. apply (de_pres regs regs' r HP). unfold DE_KR in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [de_cs|]). destruct Hr.
Qed.
(* a byte present before a run that only grows the memory is present after it *)
Lemma de_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.
Lemma de_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof.
  intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|].
  split; [exact H8|]. split; lia.
Qed.

(* ---- relay_source's afn_pre at sp = F (lib/B SEG_LATCH's lt_afn_pre_at, verbatim but for the name) ---- *)
Lemma de_afn_pre_at : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  (* sp0 is 16-aligned (astk_ok), so 8-aligned (this file's lia does not convert mod, as _drain_defs.v sets) *)
  assert (Hsp8 : sp0 mod 8 = 0).
  { assert (Hq : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    rewrite Hq. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
    pose proof HFR as (HSV & _).
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | exact Hsp8 | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* ---- the relay's table in memory: entry i's eof field (image A's dr_tbl_eof) ---- *)
Lemma de_tbl_eof : forall (W : world segs) (mem : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (i : nat),
  atable_at W mem G es tail -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (i < length es)%nat -> 0 <= re_eof (nth i es dr_e0) < 2 ^ 32 ->
  val_mem segs (arm W mem) (G + AENT * Z.of_nat i + 4) 4 (re_eof (nth i es dr_e0)).
Proof.
  intros W mem G es tail i [_ [_ Hg]] Hpad Hi Hv.
  pose proof (de_concat_entry_length es Hpad) as Hcl.
  unfold val_mem. intros k Hk.
  assert (Hj : (56 * i + (4 + k) < length (bzs (concat (map entry_bytes es) ++ tail)))%nat).
  { unfold bzs. rewrite length_map, length_app, Hcl. lia. }
  unfold garr8 in Hg. destruct (Hg _ Hj) as [Hb _]. unfold val_mem in Hb.
  specialize (Hb 0%nat ltac:(lia)).
  replace (G + AENT * Z.of_nat i + 4 + Z.of_nat k) with (G + Z.of_nat (56 * i + (4 + k)) + Z.of_nat 0)
    by (unfold AENT; lia).
  rewrite Hb. f_equal.
  assert (Hn : nth (56 * i + (4 + k)) (bzs (concat (map entry_bytes es) ++ tail)) 0 =
               bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 (re_eof (nth i es dr_e0)))) (Z_to_bv 8 0))).
  { rewrite de_nth_bzs. f_equal.
    rewrite app_nth1 by (rewrite Hcl; lia).
    rewrite de_concat_entry_nth by (first [exact Hpad | exact Hi | lia]).
    unfold entry_bytes. rewrite app_nth2 by (rewrite Mem.length_le4; lia).
    rewrite Mem.length_le4. replace (4 + k - 4)%nat with k by lia.
    rewrite app_nth1 by (rewrite Mem.length_le4; exact Hk). reflexivity. }
  rewrite Hn, de_le_byte_1_byte.
  apply bv_eq. rewrite Z_to_bv_unsigned, de_le4_le_byte by lia.
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* the paddings of every entry, from the relay's representation (aentry_ok) *)
Lemma de_pads_of_relay : forall ly S W mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es.
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & HE & _).
  rewrite Forall_forall in HE |- *. intros e He.
  destruct (HE e He) as (_ & _ & H3 & H4 & _). split; assumption.
Qed.
(* the shadow entry of a range INSIDE a live block (image A's dc_shent_block, from Reusable/YCbq.v
   shent_ok_of_block) *)
Lemma de_shent_block : forall ly S (W : world segs) mem md E Bx (mm : nat) p n q lo hi,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  U E Bx = SHADOW_OFF -> U E (SOff mm 0) = q -> p <= q + lo -> lo <= hi -> q + hi <= p + req_size n ->
  shent_ok segs Bx E (mrestrict (w_H W) mem) (mkSHE mm lo hi).
Proof.
  intros ly S W mem md E Bx mm p n q lo hi HAR Hin HB Hm Hlo Hle Hhi.
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of segs).
  destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [Hbs _].
  split.
  - destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
    eapply block_shadow_range; [exact Hbs | lia | lia].
  - destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
    intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* ------------------------------------------------------------------ the engine's seats *)
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
Definition de_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition de_Bx : sv := SOff 27 0.
(* a run's write obligation: the frame cells are in the function's own stack window, the other regions are
   read-only *)
Ltac de_awr U9 :=
  cbn [ss_mem add_cond];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold YCfn.LLVMF_STK; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.

(* (1) 0x8489c: s5 = g_s + 96 si (atom 21, seat R1), s1 = F (atom 9), s11 = SB (atom 27); the in.n cell F+144
   (written) and s->fd (atom 32, read) *)
Definition de1_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 144 152 144 152 [];
    YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))] ].
Definition de1_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (21%nat, mkAF 4096 140737479966720 3); (27%nat, mkAF SB SB 0);
            (32%nat, mkAF 0 (2 ^ 31 - 1) 0) ] [] [].
Definition ss_de1 : sstate := mkSS A_dr_arm sr_atoms de1_regions None de1_facts.
Definition de_SH1 : list shent := [ mkSHE 21 0 ASRC ].
Definition de1_extra (fd : Z) : list word := map (Z_to_bv 64) [fd].
Lemma de1_entry : forall ly S (W : world segs) regs mem md F HA fd,
  AR segs B ly S W mem md ->
  getr regs 9 = w64 F -> getr regs 21 = w64 HA -> getr regs 27 = w64 SB ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 ->
  4096 <= HA -> HA + ASRC <= SB -> HA mod 8 = 0 -> 0 <= fd < 2 ^ 31 ->
  (forall a, F + 144 <= a < F + 152 -> writable_at segs (arm W mem) a) ->
  val_mem segs (arm W mem) HA 4 fd -> azs B HA ASRC ->
  st_ok_pi segs VAL (Eimg (Ereg regs (de1_extra fd))) ss_de1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_arm)) mem (seg_rom segs)))
  /\ sh_ok segs de_Bx de_SH1 (Eimg (Ereg regs (de1_extra fd))) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md F HA fd HAR H9 H21 H27 HF1 HF2 HH0 HH1 HH2 Hfd HW1 Mfd HZ.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (de1_extra fd))).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = w64 F) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
  assert (E21 : ew E 21 = w64 HA) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
  assert (E27 : ew E 27 = w64 SB) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 fd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  split.
  - unfold ss_de1. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold de1_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply HW1; lia | apply Forall_nil].
      * rewrite E21, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ HA 0 4 (SOff 32 0) fd);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mfd.
    + apply pairwise_disjoint_of_extents. unfold de1_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E21, !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [de1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E21, E27, E32, !unsigned_lit_small by lia.
      rewrite !Z.pow_0_r, !Z.mod_1_r. try change (2 ^ 5) with 32. try change (2 ^ 3) with 8.
      repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, de_SH1. constructor; [|constructor].
    eapply shent_ok_of_range.
    + exact (azs_range_addressable B LAWS ly S W mem md HA ASRC HAR HZ).
    + unfold de_Bx. rewrite (U_atom E 27 SB E27) by lia. reflexivity.
    + rewrite (U_atom E 21 HA E21) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. assert (Hm1 : Z.min 0 ASRC = 0) by reflexivity. assert (Hm2 : Z.max 0 ASRC = ASRC) by reflexivity.
      rewrite Hm1, Hm2 in Hx. unfold ASRC in *. lia.
Qed.

(* (3n) 0x848c4 with a0 = 0: the at cell F+192 (written); a0 is the plain atom 10 (the walk splits `beqz a0` and
   refutes its fall-through edge from a0 = 0) *)
Definition de_rA : YP09.region := YP09.mkRegion (Some 9%nat) 192 200 192 200 [].
Definition de3n_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (27%nat, mkAF SB SB 0) ] [] [].
Definition ss_de3n : sstate := mkSS A_dr_ret sr_atoms [de_rA] None de3n_facts.
Lemma de3n_entry : forall (W : world segs) regs mem F,
  getr regs 9 = w64 F -> getr regs 27 = w64 SB ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 ->
  (forall a, F + 192 <= a < F + 200 -> writable_at segs (arm W mem) a) ->
  st_ok_pi segs VAL (Eimg (Ereg regs (@nil word))) ss_de3n
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)))
  /\ sh_ok segs de_Bx [] (Eimg (Ereg regs (@nil word))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F H9 H27 HF1 HF2 HWA.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (@nil word))).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = w64 F) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
  assert (E27 : ew E 27 = w64 SB) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
  assert (HSB : SB = 2147450880) by reflexivity.
  split.
  - unfold ss_de3n. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, de_rA.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply HWA; lia | apply Forall_nil].
    + cbn [pairwise_disjoint all_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [de3n_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E27, !unsigned_lit_small by lia.
      rewrite !Z.pow_0_r, !Z.mod_1_r. try change (2 ^ 5) with 32.
      repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.

(* (3f) 0x848c4 with a0 = T + 56 j (atom 10, seat R1): the at cell F+192 (written), the entry's eof field (atom 32,
   read) and its shadow entry, inside the table's live block *)
Definition de_rE : YP09.region :=
  YP09.mkRegion (Some 10%nat) 4 8 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 32 0))].
Definition de3f_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 140737479966720 3); (27%nat, mkAF SB SB 0);
            (32%nat, mkAF 0 1 0) ] [] [].
Definition ss_de3f : sstate := mkSS A_dr_ret sr_atoms [de_rA; de_rE] None de3f_facts.
Definition de_SH3 : list shent := [ mkSHE 10 0 AENT ].
Definition de3_extra (ef : Z) : list word := map (Z_to_bv 64) [ef].
Lemma de3f_entry : forall ly S (W : world segs) regs mem md F G (j : nat) ef,
  AR segs B ly S W mem md ->
  getr regs 9 = w64 F -> getr regs 10 = w64 (G + AENT * Z.of_nat j) -> getr regs 27 = w64 SB ->
  2 ^ 46 <= F <= 2 ^ 47 -> F mod 32 = 0 ->
  (forall a, F + 192 <= a < F + 200 -> writable_at segs (arm W mem) a) ->
  In (G, ATABLE) (ablocks B ly S) ->
  4096 <= G -> (G + AENT * Z.of_nat j) mod 8 = 0 -> G + ATABLE <= 140737479966720 -> G + ATABLE <= F ->
  (j < 16)%nat ->
  val_mem segs (arm W mem) (G + AENT * Z.of_nat j + 4) 4 ef -> 0 <= ef <= 1 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (de3_extra ef))) ss_de3f
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)))
  /\ sh_ok segs de_Bx de_SH3 (Eimg (Ereg regs (de3_extra ef))) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md F G j ef HAR H9 H10 H27 HF1 HF2 HWA Hin HG0 HG8 HGc HGF Hj Mef Hef.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (de3_extra ef))).
  assert (EE : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = w64 F) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
  assert (E10 : ew E 10 = w64 (G + AENT * Z.of_nat j)) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
  assert (E27 : ew E 27 = w64 SB) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 ef)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HAT : ATABLE = 896) by reflexivity. assert (HAE : AENT = 56) by reflexivity.
  split.
  - unfold ss_de3f. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, de_rA, de_rE;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply HWA; lia | apply Forall_nil].
      * rewrite E10, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (G + AENT * Z.of_nat j) 4 4 (SOff 32 0) ef);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mef].
    + apply pairwise_disjoint_of_extents. unfold de_rA, de_rE, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E10, !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [de3f_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E10, E27, E32, !unsigned_lit_small by lia.
      rewrite !Z.pow_0_r, !Z.mod_1_r. try change (2 ^ 5) with 32. try change (2 ^ 3) with 8.
      repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, de_SH3. constructor; [|constructor].
    apply (de_shent_block ly S W mem md E de_Bx 10 G ATABLE (G + AENT * Z.of_nat j) 0 AENT HAR Hin).
    + unfold de_Bx. rewrite (U_atom E 27 SB E27) by lia. reflexivity.
    + rewrite (U_atom E 10 _ E10) by lia. reflexivity.
    + lia.
    + lia.
    + replace (req_size ATABLE) with 896 by reflexivity. lia.
Qed.

(* ------------------------------------------------------------------ the stage's intermediate states *)
(* at `jal relay_source` (0x848c0, the callee's entry): in.n stored, a0 = s->fd, ra = 0x848c4 *)
Definition DE1 (cx : lfcx) (t : Z) (m : lmod) (si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_fr_relay_source)) mem (seg_rom segs)) md /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k /\
    de_ctx cx m fpos ly3 S3 W mem /\ sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
    getr regs 1 = Z_to_bv 64 (BASE + A_dr_ret) /\ getr regs 10 = w64 (hs_fd h) /\
    de_regs cx t m si (frame_addr ly3 1 fpos) regs.
(* back from relay_source (0x848c4): a0 = the entry of the source's fd, or 0 *)
Definition DE2 (cx : lfcx) (t : Z) (m : lmod) (si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
    c = mkCfg (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)) md /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k /\
    de_ctx cx m fpos ly3 S3 W mem /\ sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
    de_regs cx t m si (frame_addr ly3 1 fpos) regs /\
    ((exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
        getr regs 10 = w64 (lm_G m + AENT * Z.of_nat j)) \/
     (dr_nomatch m h (Z.of_nat (length (lm_es m))) /\ getr regs 10 = w64 0)).

(* the registers run (1) does not write (it writes a0, a1 and ra) *)
Definition DE_K1 : list (bv 5) := [2; 3; 4; 6; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* ------------------------------------------------------------------ (1) 0x8489c-0x848c0 *)
Lemma de_stage1 : forall cx t m si h fpos ly3 S3 k (W : world segs) regs mem md,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  getr regs 6 = w64 (c_n cx - dr_k' cx m) -> dr_at_op cx m -> dr_pick cx m si h ->
  SRr segs W (cfg_at segs (fr_B0 + A_dr_arm) regs mem md) (DE1 cx t m si h fpos ly3 S3 k).
Proof.
  intros cx t m si h fpos ly3 S3 k W regs mem md HB HJ HCTX HRG R6 Hatop Hpick.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  pose proof Hpick as (Hpk & Hsi & Hh).
  pose proof HMOD as (Hlen4 & HSL & _).
  pose proof (HSL si Hsi) as HSRC. unfold aslot in HSRC. rewrite Hh in HSRC.
  pose proof HSRC as (Mfd & _ & _ & _ & _ & _ & _ & _ & Rfd & _).
  assert (HAR : AR segs B ly3 S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin cx fpos ly3 S3 W mem md k HJ).
  destruct (de_spF cx HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL.
  pose proof Hatop as (Hk0 & _ & _).
  pose proof (dr_k'_rng cx m Hk0) as Hk'.
  destruct (de_slot si Hsi) as (HA0 & HA1 & HA8 & HA2).
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (HRS : rg_s fr_RG = 0x5d8e60) by reflexivity. assert (HAS : ASRC = 96) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (HZ : azs B HA ASRC)
    by (apply (de_azs_sub (rg_s fr_RG) (4 * ASRC)); [exact (dre_HZS _ _ _ _ _ _ EV) | unfold HA; lia | lia]).
  pose proof HFR as (_ & HAWR & _).
  assert (HW1 : forall a, lf_F cx + 144 <= a < lf_F cx + 152 -> writable_at segs (arm W mem) a)
    by (intros a Ha; replace a with (lf_F cx + (a - lf_F cx)) by lia; apply HAWR; lia).
  destruct (de1_entry ly3 S3 W regs mem md (lf_F cx) HA (hs_fd h) HAR C9 R21 C27 ltac:(lia) HF32 HA0
              ltac:(lia) HA8 Rfd HW1 Mfd HZ) as [HS SHOK].
  remember (Eimg (Ereg regs (de1_extra (hs_fd h)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (de1_extra (hs_fd h))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E6 : ew E 6 = w64 (c_n cx - dr_k' cx m)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6).
  assert (E9 : ew E 9 = w64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact C9).
  assert (E32 : ew E 32 = Z_to_bv 64 (hs_fd h))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  clear HE EEo.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_arm)) with (Z_to_bv 64 (BASE + A_dr_arm)).
  (* 0x8489c `beqz s5,850fc` (TRAP NONNULL) and 0x848a4 `bnez a0,850fc` (TRAP ALIGN8): both decided by the runner
     from atom 21's fact mkAF 4096 140737479966720 3 (seat R1), no W_traps.v lemma; the shadow check 0x848b8 is
     decided by mkSHE 21 0 96.  The run stores in.n, loads s->fd and stops at relay_source's entry. *)
  paj_run_to_tok RUNTO HS HJ SHOK de_span AF_fr_relay_source.
  { de_awr U9. }
  (* what the run kept: every byte outside the in.n cell, the registers but a0, a1, ra *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms) a).
  { intros a Ha (_ & Hna & _). split.
    - apply (aview_kept_out _ _ _ _ _ HFr a Ha). intros (r & Hin & Hr). cbn [ss_mem ss_de1 de1_regions In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; unfold DR_N in Hna; lia | ]).
      destruct Hin.
    - intros Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 Hp). }
  assert (WK : forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a ->
      writable_at segs (arm W (ms_mem ms)) a).
  { intros a _ Hw. apply (writable_kept (w_H W) mem (ms_mem ms) a); [|exact Hw].
    intros Hp. exact (de_pres_grows W _ _ a HG0 Hp). }
  pose proof (de_ctx_kept cx m fpos ly3 S3 W W mem (ms_mem ms) md HB HAR Hfin KEEP WK HCTX) as HCTX2.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SVN : sv8 W (ms_mem ms) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
  { unfold sv8, DR_N.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 6 0) (c_n cx - dr_k' cx m) RG0) end.
    - rewrite ?ew_ewset_other by lia. exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E6, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - zside.
    - zside. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (de1_extra (hs_fd h))) Ev)
      by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                 | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KR HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. rewrite ?E32 in Q10.
  pmkst HS.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|].
  split; [exact HJ|].
  split; [exact HCTX2|].
  split; [exact SVN|].
  split; [exact Q1|].
  split; [exact Q10|].
  exact (de_regs_kept cx t m si _ regs _ KR HRG).
Qed.

(* ------------------------------------------------------------------ (2) the call at 0x848c0: RSRC *)
Lemma de_stage2 : forall cx t m si h fpos ly3 S3 k W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> 0 <= hs_fd h < 2 ^ 31 ->
  DE1 cx t m si h fpos ly3 S3 k W c ->
  SRr segs W c (DE2 cx t m si h fpos ly3 S3 k).
Proof.
  intros cx t m si h fpos ly3 S3 k W c HB Hfd (regs & mem & md & -> & HJ & HCTX & SVN & Q1 & Q10 & HRG).
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (HAR : AR segs B ly3 S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin cx fpos ly3 S3 W mem md k HJ).
  destruct (de_spF cx HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL. pose proof de_ceil_hi as HC64.
  assert (Hsp1 : spZ regs = lf_F cx).
  { unfold spZ. rewrite C2. unfold w64. apply unsigned_lit_small. lia. }
  (* relay_source's afn_pre at sp = F; ra = 0x848c4 = BASE + 9600 *)
  assert (HRET : A_dr_ret = 9600) by reflexivity. rewrite HRET in Q1.
  destruct (de_afn_pre_at cx ly3 S3 fpos k W mem md regs RSRC_STK HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { exact C3. }
  { exact C4. }
  { exact C8. }
  { unfold RSRC_STK. lia. }
  { unfold RSRC_STK, YCfn.LLVMF_STK. lia. }
  pose proof HMOD as (_ & _ & HREL & _).
  change (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_fr_relay_source)) mem (seg_rom segs)) md)
    with (cfg_at segs (fr_B0 + AF_fr_relay_source) regs mem md).
  eapply SRr_bind.
  { exact (RSRC W ly3 S3 regs mem md ch (lm_G m) (lm_es m) (hs_fd h) HPREc Q10 ltac:(lia) HREL HRV). }
  intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & HKEEP & HA0).
  rewrite Hsp1 in HJc, HKEEP. unfold RSRC_STK in HKEEP.
  (* relay_source's journal inside this function's: ajournal_gx_sub at G_fr, the callee's lifted from G = [] *)
  assert (HJc' : ajournal_gx segs B G_fr 0 [] RSRC_STK (lf_F cx) [] ly3 S3 W mem md [] ly3 S3 W2 mem2 md2 0).
  { refine (ajournal_gx_G_mono segs B [] G_fr 0 [] RSRC_STK (lf_F cx) [] ly3 S3 W mem md [] ly3 S3 W2 mem2 md2 0 _ HJc).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k
     RSRC_STK (lf_F cx) 0 [] [] [] ly3 S3 W2 mem2 md2 0 HJ HJc'
     ltac:(unfold RSRC_STK, YCfn.LLVMF_STK; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  (* every fact of the cut, kept across the call: relay_source keeps every byte outside [F - 16, F) *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W2 mem2 a)
    by (intros a Ha (Ho & _ & _); exact (HKEEP a Ha Ho)).
  assert (WK : forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a ->
      writable_at segs (arm W2 mem2) a)
    by (intros a Ha Hw; exact (proj2 (HKEEP a ltac:(lia) ltac:(lia)) Hw)).
  pose proof (de_ctx_kept cx m fpos ly3 S3 W W2 mem mem2 md HB HAR Hfin KEEP WK HCTX) as HCTX2.
  assert (SVN2 : sv8 W2 mem2 (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
  { apply (de_sv8_kept W W2 mem mem2); [|exact SVN]. intros x Hx. apply HKEEP; unfold DR_N in Hx; lia. }
  apply SRr_ret.
  exists regs2, mem2, md2.
  split; [rewrite Q1; reflexivity|].
  split; [exact HJ2|].
  split; [exact HCTX2|].
  split; [exact SVN2|].
  split; [exact (de_regs_pres cx t m si _ regs regs2 HP2 HRG)|].
  destruct HA0 as [(j & e & Hnth & Hfde & _ & Ha0) | (Hnone & Ha0)].
  - left. exists j.
    assert (Hjl : (j < length (lm_es m))%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
    split; [exact Hjl|].
    rewrite (nth_error_nth (lm_es m) j dr_e0 Hnth). split; [exact Hfde | exact Ha0].
  - right. split; [exact (dr_nomatch_all m h Hnone) | exact Ha0].
Qed.

(* ------------------------------------------------------------------ (3) 0x848c4-0x84900 *)
(* the latch's state from what every skip path holds: the model dr_skip m k' (only the cursor moves) *)
Lemma de_mk_K : forall cx t m si h fpos ly3 S3 k (W : world segs) regs mem md,
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) ->
  de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LS cx t m ly3 S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  INV_K B G_fr fr_FP LS RINV cx t W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_LLVM_latch)) mem (seg_rom segs)) md).
Proof.
  intros cx t m si h fpos ly3 S3 k W regs mem md HJ (HFR & HFL & HMOD & HIN & HRV & HJT) SVN
    ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21)
    HSEP HLS HRI Hatop Hpick Hor.
  exists regs, mem, md. split; [reflexivity|]. split; [exact HJT|].
  exists [(1, fpos)], ly3, S3, k, (dr_skip m (dr_k' cx m)), fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|].
  split; [exact HMOD|]. split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
  split; [exact (dre_LS_drain_skip _ _ _ _ _ _ EV cx t m ly3 S3 HLS)|].
  split; [exact (dre_RI_drain_skip _ _ _ _ _ _ EV cx t m si h HRI Hatop Hpick Hor)|].
  split; [repeat split; assumption|].
  split; [exact R25|]. split; [exact Ht|]. split; [exact R20|]. split; [exact SVN|].
  exact (dr_k'_rng cx m (proj1 Hatop)).
Qed.

(* (3n) a0 = 0: `sd zero,192(s1); beqz a0,84804` *)
Lemma de_none : forall cx t m si h fpos ly3 S3 k (W : world segs) regs mem md,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LS cx t m ly3 S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) ->
  de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  dr_nomatch m h (Z.of_nat (length (lm_es m))) -> getr regs 10 = w64 0 ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)) md)
    (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t m si h fpos ly3 S3 k W regs mem md HB HSEP HLS HRI Hatop Hpick HJ HCTX SVN HRG Hnom R10.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  assert (HAR : AR segs B ly3 S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin cx fpos ly3 S3 W mem md k HJ).
  destruct (de_spF cx HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL.
  pose proof HFR as (_ & HAWR & _).
  assert (HWA : forall a, lf_F cx + 192 <= a < lf_F cx + 200 -> writable_at segs (arm W mem) a)
    by (intros a Ha; replace a with (lf_F cx + (a - lf_F cx)) by lia; apply HAWR; lia).
  destruct (de3n_entry W regs mem (lf_F cx) C9 C27 ltac:(lia) HF32 HWA) as [HS SHOK].
  remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), C9.
    apply unsigned_lit_small. lia. }
  assert (E10 : ew E 10 = w64 0).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact R10. }
  clear HE.
  (* 0x848c4 `sd zero,192(s1)`; the run stops at 0x848c8 `beqz a0,84804` (not a trap) *)
  paj_run_tok RUN HS HJ SHOK de_span.
  { unfold ss_de3n, de_rA. de_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hna. apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
    intros (r & Hin & Hr). cbn [ss_mem ss_de3n In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA] in Hr; rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
    destruct Hin. }
  psrr_branch_tok RUN BR HS SHOK de_span.
  - (* a0 = 0: to the latch *)
    paj_run_to_tok RUNTO HS HJ SHOK de_span AF_LLVM_latch.
    { unfold ss_de3n, de_rA. de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hna. rewrite <- (K1 a Ha Hna). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond ss_de3n In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA] in Hr; rewrite ?ew_ewset_other in Hr by lia;
          rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha (_ & _ & Hna); split; [exact (K2 a Ha Hna) | apply WK]).
    pose proof (de_ctx_kept cx m fpos ly3 S3 W W mem (ms_mem ms0) md HB HAR Hfin KEEP (fun a _ Hw => WK a Hw) HCTX)
      as HCTX2.
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (de_sv8_kept W W mem (ms_mem ms0)); [|exact SVN]. intros x Hx.
      unfold DR_N in Hx. split; [apply K2; [lia | unfold DR_AT; lia] | apply WK]. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (@nil word)) Ev)
        by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KR HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret.
    eapply de_mk_K; [exact HJ | exact HCTX2 | exact SVN2 | exact (de_regs_kept cx t m si _ regs _ KR HRG)
                    | exact HSEP | exact HLS | exact HRI | exact Hatop | exact Hpick | left; exact Hnom].
  - (* a0 <> 0: refuted by a0 = 0 *)
    exfalso.
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U10 : U Ev (SOff 10 0) = 0) by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E10 | lia]) end.
    rewrite W_traps.trap_br_eq, U10, U_lit in Hc by lia. cbn in Hc. discriminate Hc.
Qed.

(* the value of the image object g_lock (B: 0x5d9040), the auipc / addi pair at 0x848f4 *)
Lemma de_lock_val : VAL (A_OBJ 3) = rg_lock fr_RG.
Proof. vm_compute. reflexivity. Qed.

(* (3f) a0 = T + 56 j: the eof test, then the skip or the lock call *)
Lemma de_found : forall cx t m si h fpos ly3 S3 k (W : world segs) regs mem md j,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LS cx t m ly3 S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  de_ctx cx m fpos ly3 S3 W mem -> sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) ->
  de_regs cx t m si (frame_addr ly3 1 fpos) regs ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  getr regs 10 = w64 (lm_G m + AENT * Z.of_nat j) ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_dr_ret)) mem (seg_rom segs)) md)
    (fun W' c' => INV_K B G_fr fr_FP LS RINV cx t W' c' \/
       DLK B G_fr fr_FP LS RINV cx t m j si h fpos ly3 S3 k W' c').
Proof.
  intros cx t m si h fpos ly3 S3 k W regs mem md j HB HSEP HLS HRI Hatop Hpick HJ HCTX SVN HRG Hj Hfdj R10.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof HCTX as (HFR & HFL & HMOD & HIN & HRV & HROM).
  pose proof HRG as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & R20 & R21).
  assert (HAR : AR segs B ly3 S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  assert (Hfin : In (1, fpos) (frames S3)) by exact (de_fin cx fpos ly3 S3 W mem md k HJ).
  destruct (de_spF cx HB) as (Hsp & HFb & HF32 & Hlen & Hn).
  pose proof de_ceil as HCL.
  pose proof HMOD as (_ & _ & HREL & _).
  pose proof HREL as (_ & _ & _ & _ & _ & _ & Hle16 & HGin & (tl & HTAB) & HENT & _).
  pose proof (de_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) HREL) as HPAD.
  set (e := nth j (lm_es m) dr_e0) in *.
  assert (HEOK : aentry_ok B ly3 S3 W mem e) by (rewrite Forall_forall in HENT; apply HENT, nth_In; exact Hj).
  pose proof HEOK as (Heof01 & _).
  assert (Hef2 : 0 <= re_eof (nth j (lm_es m) dr_e0) < 2 ^ 32) by (change (nth j (lm_es m) dr_e0) with e; lia).
  assert (Mef : val_mem segs (arm W mem) (lm_G m + AENT * Z.of_nat j + 4) 4 (re_eof e))
    by (exact (de_tbl_eof W mem (lm_G m) (lm_es m) tl j HTAB HPAD Hj Hef2)).
  destruct (al_blocks _ _ LAWS ly3 S3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  assert (Hj16 : (j < 16)%nat) by lia.
  assert (HAT : ATABLE = 896) by reflexivity. assert (HAEN : AENT = 56) by reflexivity.
  assert (HSA8 : (lm_G m + AENT * Z.of_nat j) mod 8 = 0).
  { unfold AENT. pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
    rewrite D. replace (16 * (lm_G m / 16) + 56 * Z.of_nat j) with ((2 * (lm_G m / 16) + 7 * Z.of_nat j) * 8) by ring.
    apply Z_mod_mult. }
  pose proof HFR as (_ & HAWR & _).
  assert (HWA : forall a, lf_F cx + 192 <= a < lf_F cx + 200 -> writable_at segs (arm W mem) a)
    by (intros a Ha; replace a with (lf_F cx + (a - lf_F cx)) by lia; apply HAWR; lia).
  destruct (de3f_entry ly3 S3 W regs mem md (lf_F cx) (lm_G m) j (re_eof e) HAR C9 R10 C27
              ltac:(lia) HF32 HWA HGin HG4096 HSA8 ltac:(lia) ltac:(lia) Hj16 Mef ltac:(lia)) as [HS SHOK].
  remember (Eimg (Ereg regs (de3_extra (re_eof e)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (de3_extra (re_eof e))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = w64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact C9).
  assert (E10 : ew E 10 = w64 (lm_G m + AENT * Z.of_nat j)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_eof e))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  (* atom 244 = A_OBJ 3 = g_lock: the listing's auipc / addi pair at 0x848f4 resolves to it *)
  assert (ELK : ew E 244 = Z_to_bv 64 (rg_lock fr_RG)).
  { change 244%nat with (A_OBJ 3). subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite de_lock_val. reflexivity. }
  clear HE EEo.
  (* 0x848c4 `sd zero,192(s1)`; 0x848c8 `beqz a0,84804` (not a trap) decided by atom 10's lo = 4096;
     0x848d4 `bnez a0,850fc` (TRAP ALIGN8) decided by the runner from atom 10's fact mkAF 4096 140737479966720 3
     (seat R1/R2: T + 56 j is its own atom), no W_traps.v lemma; the shadow check 0x848e8 decided by
     mkSHE 10 0 56.  The run loads r->eof (atom 32) and stops at the eof test 0x848f0. *)
  paj_run_tok RUN HS HJ SHOK de_span.
  { unfold ss_de3f, de_rA, de_rE. de_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hna. apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
    intros (r & Hin & Hr). cbn [ss_mem ss_de3f In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA de_rE] in Hr; rewrite ?U9 in Hr;
        unfold DR_AT in Hna; lia | ]).
    destruct Hin. }
  (* 0x848f0 `bnez a0,84804`: the eof test (not a trap) *)
  psrr_branch_tok RUN BR HS SHOK de_span.
  - (* r->eof <> 0: end of file, the operation is a skip - to the latch *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e)
        by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hef1 : re_eof e = 1) by lia.
    paj_run_to_tok RUNTO HS HJ SHOK de_span AF_LLVM_latch.
    { unfold ss_de3f, de_rA, de_rE. de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hna. rewrite <- (K1 a Ha Hna). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond ss_de3f In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA de_rE] in Hr; rewrite ?ew_ewset_other in Hr by lia;
          rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha (_ & _ & Hna); split; [exact (K2 a Ha Hna) | apply WK]).
    pose proof (de_ctx_kept cx m fpos ly3 S3 W W mem (ms_mem ms0) md HB HAR Hfin KEEP (fun a _ Hw => WK a Hw) HCTX)
      as HCTX2.
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (de_sv8_kept W W mem (ms_mem ms0)); [|exact SVN]. intros x Hx.
      unfold DR_N in Hx. split; [apply K2; [lia | unfold DR_AT; lia] | apply WK]. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (de3_extra (re_eof e))) Ev)
        by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KR HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS.
    apply SRr_ret. left.
    eapply de_mk_K; [exact HJ | exact HCTX2 | exact SVN2 | exact (de_regs_kept cx t m si _ regs _ KR HRG)
                    | exact HSEP | exact HLS | exact HRI | exact Hatop | exact Hpick |].
    right. exists j. split; [exact Hj|]. split; [exact Hfdj | exact Hef1].
  - (* r->eof = 0: the relay still reads the source - a0 = s7 = &g_lock, `jal pthread_mutex_lock` *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e)
        by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    rename Hc into Hef0.
    paj_run_tok RUN HS HJ SHOK de_span.
    { unfold ss_de3f, de_rA, de_rE. de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hna. rewrite <- (K1 a Ha Hna). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond ss_de3f In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val de_rA de_rE] in Hr; rewrite ?ew_ewset_other in Hr by lia;
          rewrite ?U9 in Hr; unfold DR_AT in Hna; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> de_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha (_ & _ & Hna); split; [exact (K2 a Ha Hna) | apply WK]).
    pose proof (de_ctx_kept cx m fpos ly3 S3 W W mem (ms_mem ms0) md HB HAR Hfin KEEP (fun a _ Hw => WK a Hw) HCTX)
      as HCTX2.
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (de_sv8_kept W W mem (ms_mem ms0)); [|exact SVN]. intros x Hx.
      unfold DR_N in Hx. split; [apply K2; [lia | unfold DR_AT; lia] | apply WK]. }
    first [ pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0
          | pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0 ].
    cbn [ms_mem restrict] in RG0.
    assert (S192 : sv8 W (ms_mem ms0) (lf_F cx + DR_AT) 0).
    { unfold sv8, DR_AT.
      lazymatch type of RG0 with region_ok _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 192 8%N (SLit 0) 0 RG0) end.
      - rewrite ?ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - reflexivity.
      - lia.
      - lia. }
    first [ lazymatch type of HS with st_ok _ ?Ev _ _ =>
              assert (HAE2 : env_agree 32 (Ereg regs (de3_extra (re_eof e))) Ev)
                by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                           | rewrite ?ed_ewset; exact (proj2 HAE)]) end
          | lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
              assert (HAE2 : env_agree 32 (Ereg regs (de3_extra (re_eof e))) Ev)
                by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                           | rewrite ?ed_ewset; exact (proj2 HAE)]) end ].
    first [ pose proof (regs_kept_of_st_ok segs _ _ _ regs _ DE_KD HS HAE2 ltac:(vm_compute; reflexivity)) as KR
          | pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DE_KD HS HAE2
                          ltac:(vm_compute; reflexivity)) as KR ].
    cbn [ms_regs restrict] in KR.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (22%bv : bv 5) Q22.
    prreg HS (23%bv : bv 5) Q23.
    rewrite ?ELK in Q10, Q23. rewrite ?E10 in Q22.
    pmkst HS.
    apply SRr_ret. right.
    destruct HCTX2 as (HFR2 & HFL2 & HMOD2 & HIN2 & HRV2 & HROM2).
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|].
    split; [exact HJ|].
    split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HROM2|]. split; [exact HSEP|]. split; [exact HLS|].
    split; [exact HRI|]. split; [exact Hatop|]. split; [exact Hpick|]. split; [exact Hj|].
    split; [exact Hfdj|]. split; [exact Hef0|].
    split; [exact SVN2|]. split; [exact S192|].
    split; [exact Q1|]. split; [exact Q10|]. split; [exact Q23|].
    (* dr_regs_call: lregs_common but s7, s9 = t, s4 = the new cursor, s5 = the source, s6 = the entry *)
    unfold dr_regs_call.
    rewrite (KR 2%bv ltac:(de_in)), (KR 8%bv ltac:(de_in)), (KR 9%bv ltac:(de_in)), (KR 18%bv ltac:(de_in)),
      (KR 19%bv ltac:(de_in)), (KR 24%bv ltac:(de_in)), (KR 26%bv ltac:(de_in)), (KR 27%bv ltac:(de_in)),
      (KR 3%bv ltac:(de_in)), (KR 4%bv ltac:(de_in)), (KR 25%bv ltac:(de_in)), (KR 20%bv ltac:(de_in)),
      (KR 21%bv ltac:(de_in)), Q22.
    repeat split; first [assumption | lia].
Qed.

(* ------------------------------------------------------------------ (3) the three paths after the call *)
Lemma de_stage3 : forall cx t m si h fpos ly3 S3 k W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LS cx t m ly3 S3 -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  DE2 cx t m si h fpos ly3 S3 k W c ->
  SRr segs W c (fun W' c' => INV_K B G_fr fr_FP LS RINV cx t W' c' \/
    (exists m j si h fpos ly3 S3 k, DLK B G_fr fr_FP LS RINV cx t m j si h fpos ly3 S3 k W' c')).
Proof.
  intros cx t m si h fpos ly3 S3 k W c HB HSEP HLS HRI Hatop Hpick
    (regs & mem & md & -> & HJ & HCTX & SVN & HRG & [(j & Hj & Hfdj & R10) | (Hnom & R10)]).
  - eapply SRr_mono.
    { exact (de_found cx t m si h fpos ly3 S3 k W regs mem md j HB HSEP HLS HRI Hatop Hpick HJ HCTX SVN HRG
               Hj Hfdj R10). }
    intros W' c' _ [HK | HD]; [left; exact HK | right; exists m, j, si, h, fpos, ly3, S3, k; exact HD].
  - eapply SRr_mono.
    { exact (de_none cx t m si h fpos ly3 S3 k W regs mem md HB HSEP HLS HRI Hatop Hpick HJ HCTX SVN HRG
               Hnom R10). }
    intros W' c' _ HK. left. exact HK.
Qed.

(* ------------------------------------------------------------------ the stage *)
Theorem dr_stage_entry : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  INV_A B G_fr fr_FP LS RINV 2 cx t W c ->
  SRr segs W c (fun W' c' => INV_K B G_fr fr_FP LS RINV cx t W' c' \/
    (exists m j si h fpos ly3 S3 k, DLK B G_fr fr_FP LS RINV cx t m j si h fpos ly3 S3 k W' c')).
Proof.
  intros cx t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & _ & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR).
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as ((C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4) & R25 & Ht & Hk & HO & R11 & HPK).
  (* the operation is 2 (regsD's a1), so pick() ran: slot si holds h *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 2).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 2) with true in HPK.
  destruct HPK as (R20 & R6 & [(si & Hpk & R21) | (Hf & _)]); [|lia].
  change (if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) with (dr_k' cx m) in R20, R6.
  change (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) with (dr_kb cx m) in Hpk.
  pose proof HMOD as (Hlen4 & _).
  destruct (dr_pick_some (lm_hs m) (dr_kb cx m) si Hpk) as [Hsi [h Hh]].
  rewrite Hlen4 in Hsi.
  assert (HPICK : dr_pick cx m si h) by (split; [exact Hpk | split; [exact Hsi | exact Hh]]).
  assert (Hatop : dr_at_op cx m) by exact (conj Hk (conj HO Hop)).
  destruct (dre_RI_src _ _ _ _ _ _ EV cx t m si h HRI HPICK) as (_ & _ & Hfd).
  (* the arm's registers are the dispatch's but for a0 and a1 *)
  assert (HRG : de_regs cx t m si (frame_addr ly3 1 fpos) regs).
  { unfold de_regs, lregs_common.
    rewrite (KR0 2%bv ltac:(de_in)), (KR0 8%bv ltac:(de_in)), (KR0 9%bv ltac:(de_in)), (KR0 18%bv ltac:(de_in)),
      (KR0 19%bv ltac:(de_in)), (KR0 23%bv ltac:(de_in)), (KR0 24%bv ltac:(de_in)), (KR0 26%bv ltac:(de_in)),
      (KR0 27%bv ltac:(de_in)), (KR0 3%bv ltac:(de_in)), (KR0 4%bv ltac:(de_in)), (KR0 25%bv ltac:(de_in)),
      (KR0 20%bv ltac:(de_in)), (KR0 21%bv ltac:(de_in)).
    repeat split; first [assumption | lia]. }
  assert (R6' : getr regs 6 = w64 (c_n cx - dr_k' cx m)) by (rewrite (KR0 6%bv ltac:(de_in)); exact R6).
  assert (HCTX : de_ctx cx m fpos ly3 S3 W mem) by exact (conj HFR (conj HFL (conj HMOD (conj HIN (conj HRV HROM))))).
  eapply SRr_bind; [exact (de_stage1 cx t m si h fpos ly3 S3 k W regs mem md HB HJ HCTX HRG R6' Hatop HPICK)|].
  intros W1 c1 _ H1.
  eapply SRr_bind; [exact (de_stage2 cx t m si h fpos ly3 S3 k W1 c1 HB Hfd H1)|].
  intros W2 c2 _ H2.
  exact (de_stage3 cx t m si h fpos ly3 S3 k W2 c2 HB HSEP HLS HRI Hatop HPICK H2).
Qed.
End dr.
