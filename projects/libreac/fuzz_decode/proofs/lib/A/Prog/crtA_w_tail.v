(* crtA_w_tail: the last piece of the cgif-form walk of check_round_trip (image A of libreac/fuzz_decode), from the
   cut after bcmp (CRT_RET_BCMP, lib/A/Prog/crtA_cuts.v crtA_at_bcmp) to the return to the caller, landing in the
   statement's post dec_crt_post (lib/A/Prog/check_round_trip_cg.v:133).

   The walk, all at the float state fx1 the cut gives (no code here touches a float register):
     crt_seg7_F   CRT_RET_BCMP -> the free trampoline, a0 = R (bcmp answered 0, so the `bnez a0` into the abort
                  block is refuted inside the run);
     free(R)      YC5d.v:76 afree04_rule on the INNER journal of the cut (crtA_mid), o = -96, empty chain (s0 = P is
                  a heap block below sp: YG00.v:367 bad_next), trace DEC_CRT_RA_FREE1 (dec_crt_ufix);
     crt_seg8_F   -> the free trampoline, a0 = Q; free(Q) likewise, trace DEC_CRT_RA_FREE2;
     crt_seg9_F   the epilogue: ra and s0 .. s10 reloaded from the frame (crtA_frame, kept across both frees by
                  the rule's acall_kept), sp = the entry sp, the tail jump to free with a0 = P;
     free(P)      the tail free, o = 0, the entry chain ch (s0 is the caller's again; YCbq.v:281 achain_chain_pre
                  after YCbq.v:271 achain_kept), trace from crtA_pre's second trace conjunct; it returns to the
                  caller's ra.
   The post: the outer journal by YCbq.v:725 ajournal_sub (crtA_pre's journal and the inner journal at k1 = 6),
   acall_kept by YCbq.v:973 acall_kept_of_journal, the three temporaries freed (the three frees undo crtA_blocks3's
   Permutation), the meter charged dec_crt_cost.
   Every footprint run is carried into SRr by lib/A/Prog/crtA_walk.v crtA_run; the journal follows each run's
   same_but_materialized by YCbq.v:636 ajournal_exec with no written byte (the three runs write no memory). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss ExecF CrtBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YImgTop YK1b.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr DecodeList.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require LeafCgKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import crtA_iface check_round_trip_cg crtA_cuts crtA_segs crtA_walk.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.LeafCgKit.

(* ---- image-free helpers ---- *)

Lemma crtT_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

(* The registers of a state xregs_eqv to decode's `mkR` state (crtA_walk.v crtA_ms_reg), for the registers the walk
   reads. *)
Lemma crtT_regs_of : forall {x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word} {F : bvmap 5 word} {pc : word} {fc : bv 32} {rv : option word}
    {m ro : word -> option byte} {ms' : machine_state},
  ms_eqv (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                  x25 x26 x27 x28 x29 x30 x31) F pc fc rv m ro) ms' ->
  YKK.getr (ms_regs ms') 1 = x1 /\ YKK.getr (ms_regs ms') 2 = x2 /\ YKK.getr (ms_regs ms') 3 = x3 /\
  YKK.getr (ms_regs ms') 4 = x4 /\ YKK.getr (ms_regs ms') 8 = x8 /\ YKK.getr (ms_regs ms') 9 = x9 /\
  YKK.getr (ms_regs ms') 10 = x10 /\ YKK.getr (ms_regs ms') 18 = x18 /\ YKK.getr (ms_regs ms') 19 = x19 /\
  YKK.getr (ms_regs ms') 20 = x20 /\ YKK.getr (ms_regs ms') 21 = x21 /\ YKK.getr (ms_regs ms') 22 = x22 /\
  YKK.getr (ms_regs ms') 23 = x23 /\ YKK.getr (ms_regs ms') 24 = x24 /\ YKK.getr (ms_regs ms') 25 = x25 /\
  YKK.getr (ms_regs ms') 26 = x26 /\ YKK.getr (ms_regs ms') 27 = x27.
Proof.
  intros until ms'. intros H.
  repeat split; (etransitivity; [apply (crtA_ms_reg _ _ _ _ _ _ _ _ _ H); reflexivity | reflexivity]).
Qed.

(* A run that leaves sp, gp, tp, s0 .. s11 as they were keeps every callee-saved register. *)
Lemma crtT_pres : forall (regs : bvmap 5 word) {x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word}
    {F : bvmap 5 word} {pc : word} {fc : bv 32} {rv : option word} {m ro : word -> option byte}
    {ms' : machine_state},
  ms_eqv (MS (mkR x1 (YKK.getr regs (Z_to_bv 5 2)) (YKK.getr regs (Z_to_bv 5 3)) (YKK.getr regs (Z_to_bv 5 4))
                  x5 x6 x7 (YKK.getr regs (Z_to_bv 5 8)) (YKK.getr regs (Z_to_bv 5 9)) x10 x11 x12 x13 x14 x15 x16
                  x17 (YKK.getr regs (Z_to_bv 5 18)) (YKK.getr regs (Z_to_bv 5 19)) (YKK.getr regs (Z_to_bv 5 20))
                  (YKK.getr regs (Z_to_bv 5 21)) (YKK.getr regs (Z_to_bv 5 22)) (YKK.getr regs (Z_to_bv 5 23))
                  (YKK.getr regs (Z_to_bv 5 24)) (YKK.getr regs (Z_to_bv 5 25)) (YKK.getr regs (Z_to_bv 5 26))
                  (YKK.getr regs (Z_to_bv 5 27)) x28 x29 x30 x31) F pc fc rv m ro) ms' ->
  aregs_preserved regs (ms_regs ms').
Proof.
  intros regs. intros until ms'. intros H r Hr. unfold acallee_saved in Hr.
  destruct (crtT_regs_of H) as (_ & G2 & G3 & G4 & G8 & G9 & _ & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 &
    G26 & G27).
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    assumption.
Qed.

Lemma crtT_sp_of : forall (rg : bvmap 5 word) (v : word) (z : Z),
  YKK.getr rg 2 = v -> v = w64 z -> 0 <= z < 2 ^ 64 -> spZ rg = z.
Proof. intros rg v z H1 H2 Hz. unfold spZ. rewrite H1, H2. apply crtT_u64. exact Hz. Qed.

Lemma crtT_s0_of : forall (rg : bvmap 5 word) (v : word) (z : Z),
  YKK.getr rg 8 = v -> v = w64 z -> 0 <= z < 2 ^ 64 -> s0Z rg = z.
Proof. intros rg v z H1 H2 Hz. unfold s0Z. rewrite H1, H2. apply crtT_u64. exact Hz. Qed.

(* Every loaded segment of image A lies below kLowMemEnd (YImgTop.v's computed image bounds). *)
Lemma crtT_segs_low : forall a, in_img decodesegs0 a -> 0 <= a < kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr).
  pose proof YImgTop.segs_in_asan as Hall. unfold YImgTop.segs_in in Hall. rewrite forallb_forall in Hall.
  pose proof (Hall sg Hin) as Hb. apply andb_true_iff in Hb as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. unfold YImgTop.seg_lo, YImgTop.seg_hi in Hlo, Hhi.
  pose proof YImgTop.IMG_LO_val as E1. pose proof YImgTop.IMG_TOP_val as E2. unfold kLowMemEnd. lia.
Qed.

Lemma crtT_perm_dup : forall {X : Type} (l rest : list X) (x : X),
  Permutation l (x :: rest) -> In x rest -> exists l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3.
Proof.
  intros X l rest x HP Hin.
  assert (Hx : In x l) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  apply in_split in Hx as (a & b & ->).
  assert (HP2 : Permutation rest (a ++ b)) by (eapply Permutation_cons_app_inv; apply Permutation_sym; exact HP).
  pose proof (Permutation_in _ HP2 Hin) as Hin2.
  apply in_app_or in Hin2 as [Ha | Hb].
  - apply in_split in Ha as (c & d & ->). exists c, d, b. rewrite <- app_assoc. reflexivity.
  - apply in_split in Hb as (c & d & ->). exists a, c, d. reflexivity.
Qed.

Lemma crtT_perm_rm : forall {X : Type} (l1 l2 rest : list X) (x : X),
  Permutation (l1 ++ x :: l2) (x :: rest) -> Permutation (l1 ++ l2) rest.
Proof.
  intros X l1 l2 rest x H. apply Permutation_sym. eapply Permutation_cons_app_inv. apply Permutation_sym. exact H.
Qed.

(* The trace a call rule asks for (YCbq.v:317 call_trace0) is the statement's dec_utrace of the return addresses. *)
Lemma crtT_trace : forall pc0 regsT ch, call_trace0 pc0 regsT ch = dec_utrace pc0 (raZ regsT :: spine ch).
Proof.
  intros pc0 regsT ch. unfold call_trace0, unwind_of_chain, dec_utrace, spine. cbn [flat_map map].
  f_equal. f_equal. f_equal.
  induction ch as [|[[fp ra] nfp] ch IH]; [reflexivity|]. cbn [flat_map map]. f_equal. exact IH.
Qed.

(* s0 below sp: the chain the allocator walks is empty (YG00.v:367 bad_next). *)
Lemma crtT_chain_nil : forall ly rd (regsT : bvmap 5 word),
  4096 <= raZ regsT -> s0Z regsT <= spZ regsT -> chain_pre ly rd regsT [].
Proof.
  intros ly rd regsT Hra Hs. unfold chain_pre. split; [exact Hra|].
  destruct (frame0_ok ly regsT); [|reflexivity].
  unfold bad_next. replace (s0Z regsT <=? spZ regsT) with true by (symmetry; apply Z.leb_le; exact Hs).
  reflexivity.
Qed.

Lemma crtT_mem_eq : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  apresent H m a -> apresent H' m' a -> aview decodesegs0 H' m' a = aview decodesegs0 H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
  unfold aview, OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YP09.mbyte, mrestrict in E.
  rewrite Hh, Hh' in E. rewrite Hb, Hb' in E. cbn in E.
  injection E as E. rewrite Hb, Hb'. f_equal. apply bv_eq. exact E.
Qed.

Lemma crtT_rw_cells_ext : forall (m m' : word -> option byte) (A : Z) (cs : list cell),
  rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (Wa & Wl & Hw)] He.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
    assert (Hi' : A <= A + Z.of_nat i < A + Z.of_nat (cells_size cs)) by (rewrite <- L; lia).
    unfold mrd. rewrite (He _ Hi'). exact (Hb i Hi).
  - split; [exact Wa|]. split; [exact Wl|]. intros i Hi.
    unfold wview. rewrite (He (A + i)) by lia. exact (Hw i Hi).
Qed.

(* The frame the prologue wrote survives every step that keeps its 96 bytes present and their view. *)
Lemma crtT_frame_keep : forall (regs : bvmap 5 word) (m m' : word -> option byte) (H H' : word -> bool),
  crtA_frame regs m ->
  (forall a, spZ regs - CRT_FRAME <= a < spZ regs - CRT_FRAME + 96 ->
     apresent H m a /\ apresent H' m' a /\ aview decodesegs0 H' m' a = aview decodesegs0 H m a) ->
  crtA_frame regs m'.
Proof.
  intros regs m m' H H' F K. unfold crtA_frame in *.
  apply (crtT_rw_cells_ext m m' _ _ F). intros a Ha.
  assert (S96 : forall c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra,
    Z.of_nat (cells_size (crt_fr c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)) = 96) by reflexivity.
  rewrite S96 in Ha.
  destruct (K a Ha) as (P1 & P2 & E). unfold wa. exact (crtT_mem_eq H H' m m' a P1 P2 E).
Qed.

Section TailHelpers.
Context {rc : YM05.RunCeil}.

Lemma crtT_frame_step : forall (regs : bvmap 5 word) (Ha Hb : word -> bool) (ma mb : word -> option byte)
    (slo shi : Z),
  crtA_frame regs ma ->
  (forall a, spZ regs - DEC_CRT_STK <= a < spZ regs -> apresent Ha ma a) ->
  (forall a, spZ regs - DEC_CRT_STK <= a < spZ regs -> apresent Hb mb a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) ->
     aview decodesegs0 Hb mb a = aview decodesegs0 Ha ma a) ->
  alloc_ceiling <= spZ regs - CRT_FRAME -> spZ regs < 2 ^ 64 -> shi <= spZ regs - CRT_FRAME ->
  crtA_frame regs mb.
Proof.
  intros regs Ha Hb ma mb slo shi F PA PB K H1 H2 H3.
  assert (ES : DEC_CRT_STK = 96 + 16384) by reflexivity. assert (EF : CRT_FRAME = 96) by reflexivity.
  apply (crtT_frame_keep regs ma mb Ha Hb F). intros a Hr.
  split; [apply PA; lia|]. split; [apply PB; lia|]. apply K; lia.
Qed.

(* A run's footprint over the frame: the frame bytes lie in the inner journal's window, where every byte is
   present, hence not hidden. *)
Lemma crtT_rng_frame : forall (W : world decodesegs0) (mem : word -> option byte) (lo : Z),
  0 <= lo -> lo + 96 <= 2 ^ 64 -> (forall a, lo <= a < lo + 96 -> apresent (w_H W) mem a) ->
  ExecF.rng (LCK.RNG_W (world decodesegs0) (@w_H decodesegs0) W) lo 96.
Proof.
  intros W mem lo H0 H1 HP. split; [exact H0|]. split; [exact H1|]. intros b j Hb Hj.
  unfold LCK.RNG_W, LCK.range_avoids, LCK.woff. intros kk Hk.
  rewrite (crtT_u64 b) by lia.
  destruct (HP (b + Z.of_nat kk) ltac:(lia)) as [Hh _]. exact Hh.
Qed.
End TailHelpers.

(* The return addresses of the two inner frees, and their parity (YK0s.v:204 ret_ok_even). *)
Lemma crtT_ra1 : bv_unsigned (Z_to_bv 64 (CRT_AT 0x224)) = DEC_CRT_RA_FREE1 /\
  bv_unsigned (Z_to_bv 64 (CRT_AT 0x224)) mod 2 = 0 /\ 4096 <= bv_unsigned (Z_to_bv 64 (CRT_AT 0x224)).
Proof. split; [|split]; vm_compute; first [reflexivity | discriminate]. Qed.

Lemma crtT_ra2 : bv_unsigned (Z_to_bv 64 (CRT_AT 0x22c)) = DEC_CRT_RA_FREE2 /\
  bv_unsigned (Z_to_bv 64 (CRT_AT 0x22c)) mod 2 = 0 /\ 4096 <= bv_unsigned (Z_to_bv 64 (CRT_AT 0x22c)).
Proof. split; [|split]; vm_compute; first [reflexivity | discriminate]. Qed.

Section Tail.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := decodesegs0.
Local Notation sink := dec_A_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RO_RD : list (Z * Z).
Local Notation ajournalA := (@ajournal rc sink segs B).
Hypothesis HFPC : pc_wrap_free (as_code B) = decode_sigma DS___interceptor_trampoline_free.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AFREE : forall fx' : YK11.FPState, @afree04_rule fx' rc sink segs B MT.

(* A footprint run writes no memory: the journal follows its same_but_materialized (YCbq.v:636, Wr = False). *)
Lemma crtT_aj_md : forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> same_but_materialized mdc mdc' ->
  ajournalA STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  eapply (ajournal_exec segs B LAWS crtT_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc mdc'
            (fun _ => False) HJ).
  - intros x _. reflexivity.
  - apply YK1b.mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a Ha. destruct Ha.
Qed.

(* A block listed in front of `rest` in a permutation of the live blocks is not also in `rest`: AR keeps the
   live blocks pairwise disjoint (YCbq.v:712 sep_blocks_pos), and a block of positive size meets itself. *)
Lemma crtT_not_old : forall ly S W m md (x : Z * Z) rest,
  AR segs B ly S W m md -> Permutation (ablocks B ly S) (x :: rest) -> 0 < snd x -> ~ In x rest.
Proof.
  intros ly S W m md [p n] rest HAR HP Hn Hin. cbn [snd] in Hn.
  destruct (crtT_perm_dup _ _ _ HP Hin) as (l1 & l2 & l3 & E).
  pose proof (sep_blocks_pos segs B LAWS ly S W m md (p, n) (p, n) l1 l2 l3 HAR E) as D.
  unfold zdisjoint, block_rng, req_size in D. cbn [fst snd] in D.
  replace (n =? 0) with false in D by (symmetry; apply Z.eqb_neq; lia). lia.
Qed.

(* One free inside the walk: afree04_rule on the inner journal of the cut (stack window
   [sp - DEC_CRT_STK, sp), no footprint, base state lyc Sc), for a block the call allocated. *)
Lemma crtT_free : forall (fx1 : YKK.FPState) (sp : Z) (lyc : alayout) (Sc : astate) (W : world segs)
    (memc : word -> option byte) (mdc : Model) (Wc : world segs) (regsT : bvmap 5 word)
    (memT : word -> option byte) (mdT : Model) (ly1 : alayout) (S1 : astate) (k1 pa n o : Z) (raw : word)
    (ch : list (Z * Z * Z)) (Qp : world segs -> config -> Prop),
  ajournalA DEC_CRT_STK sp [] lyc Sc W memc mdc [] ly1 S1 Wc memT mdT k1 ->
  In (pa, n) (ablocks B ly1 S1) -> ~ In (pa, n) (ablocks B lyc Sc) ->
  YKK.getr regsT 10 = w64 pa ->
  spZ regsT = sp + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= DEC_CRT_STK ->
  YKK.getr regsT 3 = w64 (as_gp B) -> YKK.getr regsT 4 = w64 (as_tp B) ->
  YKK.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  st_nev S1 < EV_MAX ->
  chain_pre ly1 (aview segs (w_H Wc) memT) regsT ch ->
  In (call_trace0 (pc_free_ra0 (as_code B)) regsT ch) (as_universe B) ->
  mo_ok MT S1 (mo_free MT) ->
  (forall W2 ly2 S2 regs2 mem2 md2,
     ajournalA DEC_CRT_STK sp [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 (k1 + 1) ->
     aregs_preserved regsT regs2 ->
     (exists l1 l2, ablocks B ly1 S1 = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) ->
     frames S2 = frames S1 ->
     acall_kept segs B ly1 S1 Wc memT W2 mem2 (sp + o - ASTACK) (sp + o) (fun a => pa <= a < pa + req_size n) ->
     mo_le MT S1 S2 (mo_free MT) ->
     SRr segs W2 (mkCfg (@YKK.mkst fx1 regs2 raw mem2 (YKK.seg_rom segs)) md2) Qp) ->
  SRr segs Wc (mkCfg (@YKK.mkst fx1 regsT (Z_to_bv 64 CRT_FREE) memT (YKK.seg_rom segs)) mdT) Qp.
Proof.
  intros fx1 sp lyc Sc W memc mdc Wc regsT memT mdT ly1 S1 k1 pa n o raw ch Qp
    HJ Hin Hnot Ha0 Hsp Ho16 Ho0 Hstk Hgp Htp Hra Hrok Hnev Hch Htr Hmo K.
  assert (EF : CRT_FREE = pc_wrap_free (as_code B)) by (rewrite HFPC; reflexivity).
  rewrite EF.
  eapply SRr_bind.
  - exact (AFREE fx1 Wc regsT memT DEC_CRT_STK sp [] lyc Sc W memc mdc [] ly1 S1 mdT k1 pa n o raw ch
             HJ Hin Ha0 Hsp Ho16 Ho0 Hstk Hgp Htp Hra Hrok Hnev Hch Htr
             (fun H => False_ind _ (Hnot H)) Hmo).
  - intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HRP & HBL & HFR & HK & HML).
    exact (K W2 ly2 S2 regs2 mem2 md2 HJ2 HRP HBL HFR HK HML).
Qed.

Ltac crtT_cs := unfold acallee_saved; lia.

Theorem crtA_tail : crtA_at_bcmp B MT RO_RD.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
         ly1 S1 W1 mem1 md1 regs1 P Q R fx1 PRE MID REGS A01 BLK FRM.
  destruct PRE as (OJ & RET & RA4096 & GP & TP & _ & _ & _ & _ & ACH & _ & SPLO & SPHI & _ & NCH & NS & BND & _ &
    _ & _ & _ & _ & _ & _ & NEV & _ & MOK & COST & _ & TR2 & UFIX & _ & _).
  destruct UFIX as (_ & _ & U3 & U4).
  destruct MID as (IJ & FRS1 & MLE1 & FR1 & _).
  destruct REGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R23 & R24 & R27).
  destruct BLK as (PERM & P0 & Q0 & R0).
  assert (EST : DEC_CRT_STK = 96 + 16384) by reflexivity.
  assert (EAS : ASTACK = 16384) by reflexivity.
  assert (EEV : DEC_CRT_EV = 6) by reflexivity.
  assert (ECF : CRT_FRAME = 96) by reflexivity.
  rewrite EEV in NEV.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL _].
  pose proof OJ as (HARc & _ & _ & _ & _ & _ & HNEVc & _).
  pose proof IJ as (HAR1 & _ & _ & _ & _ & _ & HNEV1 & _ & _ & _ & _ & _ & _ & HPRES1 & HSTK & _ & _).
  destruct HSTK as (_ & _ & HCEIL & HSLO & HSHI & H47 & _ & HTOP2 & HTOP).
  assert (SPB : alloc_ceiling + 96 + 16384 <= spZ regs <= 2 ^ 47) by lia.
  assert (NN : 1 <= nch * ns <= 1524) by nia.
  (* the three temporaries *)
  assert (INR1 : In (R, 3 * (nch * ns)) (ablocks B ly1 S1))
    by (apply (Permutation_in _ (Permutation_sym PERM)); left; reflexivity).
  assert (INQ1 : In (Q, 8 * nch) (ablocks B ly1 S1))
    by (apply (Permutation_in _ (Permutation_sym PERM)); right; left; reflexivity).
  assert (INP1 : In (P, 4 * (nch * ns)) (ablocks B ly1 S1))
    by (apply (Permutation_in _ (Permutation_sym PERM)); right; right; left; reflexivity).
  assert (NR : ~ In (R, 3 * (nch * ns)) (ablocks B lyc Sc)).
  { intros H. exact (crtT_not_old ly1 S1 W1 mem1 md1 _ _ HAR1 PERM ltac:(cbn [snd]; lia)
                       (or_intror (or_intror H))). }
  assert (NQ : ~ In (Q, 8 * nch) (ablocks B lyc Sc)).
  { intros H. refine (crtT_not_old ly1 S1 W1 mem1 md1 (Q, 8 * nch)
      ((R, 3 * (nch * ns)) :: (P, 4 * (nch * ns)) :: ablocks B lyc Sc) HAR1 _ ltac:(cbn [snd]; lia)
      (or_intror (or_intror H))).
    eapply Permutation_trans; [exact PERM | apply perm_swap]. }
  assert (NP : ~ In (P, 4 * (nch * ns)) (ablocks B lyc Sc)).
  { intros H. refine (crtT_not_old ly1 S1 W1 mem1 md1 (P, 4 * (nch * ns))
      ((R, 3 * (nch * ns)) :: (Q, 8 * nch) :: ablocks B lyc Sc) HAR1 _ ltac:(cbn [snd]; lia)
      (or_intror (or_intror H))).
    eapply Permutation_trans; [exact PERM|].
    eapply Permutation_trans; [apply perm_skip; apply perm_swap | apply perm_swap]. }
  pose proof (al_blocks _ _ LAWS ly1 S1 W1 mem1 md1 P (4 * (nch * ns)) HAR1 INP1) as (_ & _ & PB & _).
  assert (PLT : P <= alloc_ceiling).
  { unfold req_size in PB. replace (4 * (nch * ns) =? 0) with false in PB by (symmetry; apply Z.eqb_neq; lia).
    lia. }
  assert (SPF : bv_unsigned (YKK.getr regs1 (Z_to_bv 5 2)) = spZ regs - CRT_FRAME).
  { transitivity (bv_unsigned (w64 (spZ regs - CRT_FRAME))); [exact (f_equal (@bv_unsigned 64) R2)|].
    apply crtT_u64. lia. }

  (* ---- seg7: CRT_RET_BCMP (a0 = 0) -> free(R) ---- *)
  eapply (@crtA_run fx1 W1 regs1 mem1 md1 CRT_RET_BCMP).
  { unfold LCK.ms_of_regs. eapply crt_seg7_F. exact A01. }
  intros ms7 md7 (ms0 & -> & EQV7) SBM7.
  destruct (crtT_regs_of EQV7) as (G7_1 & G7_2 & G7_3 & G7_4 & G7_8 & _ & G7_10 & _).
  pose proof (crtT_pres regs1 EQV7) as RP7.
  rewrite (@crtA_ms_shape fx1 _ _ _ _ EQV7).
  pose proof (crtT_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJ SBM7) as IJ7.
  apply (crtT_free fx1 (spZ regs) lyc Sc W memc mdc W1 (ms_regs ms7) mem1 md7 ly1 S1 3 R (3 * (nch * ns)) (-96)
           (Z_to_bv 64 (CRT_AT 0x224)) [] _ IJ7 INR1 NR).
  { rewrite G7_10. exact R23. }
  { apply (crtT_sp_of _ _ _ G7_2 R2). lia. }
  { reflexivity. }
  { lia. }
  { rewrite EAS, EST. lia. }
  { rewrite G7_3. etransitivity; [exact R3 | exact GP]. }
  { rewrite G7_4. etransitivity; [exact R4 | exact TP]. }
  { exact G7_1. }
  { apply YK0s.ret_ok_even. exact (proj1 (proj2 crtT_ra1)). }
  { lia. }
  { apply crtT_chain_nil.
    - unfold raZ. rewrite G7_1. exact (proj2 (proj2 crtT_ra1)).
    - rewrite (crtT_s0_of _ _ _ G7_8 R8) by lia. rewrite (crtT_sp_of _ _ _ G7_2 R2) by lia. lia. }
  { rewrite crtT_trace. cbn [spine map].
    replace (raZ (ms_regs ms7)) with DEC_CRT_RA_FREE1; [exact U3|].
    unfold raZ. rewrite G7_1. exact (proj1 crtT_ra1). }
  { apply (mok_station MT Sc S1 T (crtA_acc3 MT nch ns) (mo_free MT) MTL MOK MLE1 (mo_free_nonneg MT MTL)).
    unfold crtA_acc3. unfold dec_crt_cost in COST. pose proof (mo_free_nonneg MT MTL). lia. }
  intros W2 ly2 S2 regs2 mem2 md2 IJ2 RPF1 BLF1 FRF1 KF1 MLF1.
  pose proof IJ2 as (_ & _ & _ & _ & _ & _ & HNEV2 & _ & _ & _ & _ & _ & _ & HPRES2 & _ & _ & _).
  assert (FR2 : crtA_frame regs mem2).
  { apply (crtT_frame_step regs (w_H W1) (w_H W2) mem1 mem2 (spZ regs + -96 - ASTACK) (spZ regs + -96) FR1 HPRES1
             HPRES2 (proj1 KF1)); lia. }
  assert (PERM2 : Permutation (ablocks B ly2 S2) ((Q, 8 * nch) :: (P, 4 * (nch * ns)) :: ablocks B lyc Sc)).
  { destruct BLF1 as (l1 & l2 & E1 & E2). rewrite E2. rewrite E1 in PERM. exact (crtT_perm_rm _ _ _ _ PERM). }
  assert (INQ2 : In (Q, 8 * nch) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym PERM2)); left; reflexivity).
  pose proof (mle_station MT Sc S1 S2 _ _ MTL MLE1 MLF1) as MLE2.
  pose proof (aregs_preserved_trans _ _ _ RP7 RPF1) as CS2.
  clear IJ7 KF1 BLF1 MLF1.

  (* ---- seg8: CRT_RET_FREE1 -> free(Q) ---- *)
  eapply (@crtA_run fx1 W2 regs2 mem2 md2 CRT_RET_FREE1).
  { unfold LCK.ms_of_regs. eapply crt_seg8_F. }
  intros ms8 md8 (ms0 & -> & EQV8) SBM8.
  destruct (crtT_regs_of EQV8) as (G8_1 & G8_2 & G8_3 & G8_4 & G8_8 & _ & G8_10 & _).
  pose proof (crtT_pres regs2 EQV8) as RP8.
  rewrite (@crtA_ms_shape fx1 _ _ _ _ EQV8).
  pose proof (crtT_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJ2 SBM8) as IJ8.
  apply (crtT_free fx1 (spZ regs) lyc Sc W memc mdc W2 (ms_regs ms8) mem2 md8 ly2 S2 (3 + 1) Q (8 * nch) (-96)
           (Z_to_bv 64 (CRT_AT 0x22c)) [] _ IJ8 INQ2 NQ).
  { rewrite G8_10. rewrite (CS2 21 ltac:(crtT_cs)). exact R21. }
  { apply (crtT_sp_of _ _ _ G8_2 (eq_trans (CS2 2 ltac:(crtT_cs)) R2)). lia. }
  { reflexivity. }
  { lia. }
  { rewrite EAS, EST. lia. }
  { rewrite G8_3, (CS2 3 ltac:(crtT_cs)). etransitivity; [exact R3 | exact GP]. }
  { rewrite G8_4, (CS2 4 ltac:(crtT_cs)). etransitivity; [exact R4 | exact TP]. }
  { exact G8_1. }
  { apply YK0s.ret_ok_even. exact (proj1 (proj2 crtT_ra2)). }
  { lia. }
  { apply crtT_chain_nil.
    - unfold raZ. rewrite G8_1. exact (proj2 (proj2 crtT_ra2)).
    - rewrite (crtT_s0_of _ _ _ G8_8 (eq_trans (CS2 8 ltac:(crtT_cs)) R8)) by lia.
      rewrite (crtT_sp_of _ _ _ G8_2 (eq_trans (CS2 2 ltac:(crtT_cs)) R2)) by lia. lia. }
  { rewrite crtT_trace. cbn [spine map].
    replace (raZ (ms_regs ms8)) with DEC_CRT_RA_FREE2; [exact U4|].
    unfold raZ. rewrite G8_1. exact (proj1 crtT_ra2). }
  { apply (mok_station MT Sc S2 T (crtA_acc3 MT nch ns + mo_free MT) (mo_free MT) MTL MOK MLE2
             (mo_free_nonneg MT MTL)).
    unfold crtA_acc3. unfold dec_crt_cost in COST. pose proof (mo_free_nonneg MT MTL). lia. }
  intros W3 ly3 S3 regs3 mem3 md3 IJ3 RPF2 BLF2 FRF2 KF2 MLF2.
  pose proof IJ3 as (_ & HLY3 & _ & _ & _ & _ & HNEV3 & _ & HKEEP3 & _ & _ & _ & _ & HPRES3 & _ & _ & _).
  assert (FR3 : crtA_frame regs mem3).
  { apply (crtT_frame_step regs (w_H W2) (w_H W3) mem2 mem3 (spZ regs + -96 - ASTACK) (spZ regs + -96) FR2 HPRES2
             HPRES3 (proj1 KF2)); lia. }
  assert (PERM3 : Permutation (ablocks B ly3 S3) ((P, 4 * (nch * ns)) :: ablocks B lyc Sc)).
  { destruct BLF2 as (l1 & l2 & E1 & E2). rewrite E2. rewrite E1 in PERM2. exact (crtT_perm_rm _ _ _ _ PERM2). }
  assert (INP3 : In (P, 4 * (nch * ns)) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym PERM3)); left; reflexivity).
  pose proof (mle_station MT Sc S2 S3 _ _ MTL MLE2 MLF2) as MLE3.
  pose proof (aregs_preserved_trans _ _ _ CS2 (aregs_preserved_trans _ _ _ RP8 RPF2)) as CS3.
  clear IJ8 KF2 BLF2 MLF2.

  (* ---- seg9: the epilogue, CRT_RET_FREE2 -> the tail jump to free(P) ---- *)
  assert (SP3 : bv_unsigned (YKK.getr regs3 (Z_to_bv 5 2)) = spZ regs - CRT_FRAME).
  { rewrite (CS3 2 ltac:(crtT_cs)). exact SPF. }
  assert (FR3' := FR3). unfold crtA_frame in FR3'. rewrite <- SP3 in FR3'.
  eapply (@crtA_run fx1 W3 regs3 mem3 md3 CRT_RET_FREE2).
  { unfold LCK.ms_of_regs. eapply crt_seg9_F.
    - exact FR3'.
    - rewrite SP3. lia.
    - rewrite SP3. apply (crtT_rng_frame W3 mem3); [lia | lia |]. intros a Ha. apply HPRES3. lia. }
  intros ms9 md9 (ms0 & -> & EQV9) SBM9.
  destruct (crtT_regs_of EQV9) as (G9_1 & G9_2 & G9_3 & G9_4 & G9_8 & G9_9 & G9_10 & G9_18 & G9_19 & G9_20 &
    G9_21 & G9_22 & G9_23 & G9_24 & G9_25 & G9_26 & G9_27).
  assert (CS9 : aregs_preserved regs (ms_regs ms9)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - etransitivity; [exact G9_2|]. rewrite SP3, ECF. replace (spZ regs - 96 + 96) with (spZ regs) by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - etransitivity; [exact G9_3|]. rewrite (CS3 3 ltac:(crtT_cs)). exact R3.
    - etransitivity; [exact G9_4|]. rewrite (CS3 4 ltac:(crtT_cs)). exact R4.
    - exact G9_8.
    - exact G9_9.
    - exact G9_18.
    - exact G9_19.
    - exact G9_20.
    - exact G9_21.
    - exact G9_22.
    - exact G9_23.
    - exact G9_24.
    - exact G9_25.
    - exact G9_26.
    - etransitivity; [exact G9_27|]. rewrite (CS3 27 ltac:(crtT_cs)). exact R27. }
  assert (SP9 : spZ (ms_regs ms9) = spZ regs) by exact (f_equal (@bv_unsigned 64) (CS9 2 ltac:(crtT_cs))).
  rewrite (@crtA_ms_shape fx1 _ _ _ _ EQV9).
  pose proof (crtT_aj_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IJ3 SBM9) as IJ9.

  (* ---- the tail free(P): returns to the caller's ra ---- *)
  apply (crtT_free fx1 (spZ regs) lyc Sc W memc mdc W3 (ms_regs ms9) mem3 md9 ly3 S3 (3 + 1 + 1) P
           (4 * (nch * ns)) 0 (YKK.getr regs 1) ch _ IJ9 INP3 NP).
  { rewrite G9_10. rewrite (CS3 8 ltac:(crtT_cs)). exact R8. }
  { rewrite SP9. lia. }
  { reflexivity. }
  { lia. }
  { rewrite EAS, EST. lia. }
  { etransitivity; [exact (CS9 3 ltac:(crtT_cs)) | exact GP]. }
  { etransitivity; [exact (CS9 4 ltac:(crtT_cs)) | exact TP]. }
  { exact G9_1. }
  { exact RET. }
  { lia. }
  { apply (achain_chain_pre ly3 _ (spZ regs) (s0Z regs) ch (ms_regs ms9)).
    - destruct HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & ETOP & _).
      apply (achain_ly_top lyc ly3 _ _ _ _ ETOP).
      apply (achain_kept lyc (aview segs (w_H W) memc) _ (spZ regs) (s0Z regs) ch (spZ regs) ACH); [lia | lia |].
      intros a Ha. apply HKEEP3; lia.
    - rewrite SP9. lia.
    - exact (f_equal (@bv_unsigned 64) (CS9 8 ltac:(crtT_cs))).
    - unfold raZ in *. rewrite G9_1. exact RA4096. }
  { rewrite crtT_trace.
    replace (raZ (ms_regs ms9)) with (raZ regs); [exact TR2|].
    unfold raZ. rewrite G9_1. reflexivity. }
  { apply (mok_station MT Sc S3 T (crtA_acc3 MT nch ns + mo_free MT + mo_free MT) (mo_free MT) MTL MOK MLE3
             (mo_free_nonneg MT MTL)).
    unfold crtA_acc3. unfold dec_crt_cost in COST. pose proof (mo_free_nonneg MT MTL). lia. }
  intros W4 ly4 S4 regs4 mem4 md4 IJ4 RPF3 BLF3 FRF3 _ MLF3.
  assert (PERM4 : Permutation (ablocks B ly4 S4) (ablocks B lyc Sc)).
  { destruct BLF3 as (l1 & l2 & E1 & E2). rewrite E2. rewrite E1 in PERM3. exact (crtT_perm_rm _ _ _ _ PERM3). }
  apply SRr_ret. unfold dec_crt_post.
  exists fx1, ly4, S4, regs4, mem4, md4.
  split; [reflexivity|].
  split; [exact FRM|].
  split.
  { pose proof (ajournal_sub segs B LAWS crtT_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  DEC_CRT_STK (spZ regs) [] [] ly4 S4 W4 mem4 md4 (3 + 1 + 1 + 1) OJ IJ4 SPLO SPHI
                  ltac:(intros a (r & Hr & _); destruct Hr)) as J.
    cbn [app] in J. replace (k + DEC_CRT_EV) with (k + (3 + 1 + 1 + 1)) by (rewrite EEV; lia). exact J. }
  split; [exact (aregs_preserved_trans _ _ _ CS9 RPF3)|].
  split; [rewrite FRF3, FRF2, FRF1; exact FRS1|].
  split; [exact PERM4|].
  split.
  { apply (acall_kept_of_journal segs B crtT_segs_low DEC_CRT_STK (spZ regs) [] [] lyc Sc W memc mdc ly4 S4 W4 mem4
             md4 (3 + 1 + 1 + 1) (fun _ => False) IJ4 HARc).
    - intros a (r & Hr & _). destruct Hr.
    - intros b m i Hb _ _. exact (Permutation_in _ (Permutation_sym PERM4) Hb).
    - exact sink_closed_nil. }
  pose proof (mle_station MT Sc S3 S4 _ _ MTL MLE3 MLF3) as MLE4.
  apply (mle_weaken MT Sc S4 _ _ MTL MLE4). unfold dec_crt_cost, crtA_acc3. lia.
Qed.
End Tail.
