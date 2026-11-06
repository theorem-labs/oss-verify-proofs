(* check_latest_sent_cgW: Theorem transport_check_latest_sent_cg_holds : the statement
   transport_check_latest_sent_cg_holds_stmt of lib/B/Prog/check_latest_sent_cg.v, the caller-journal walk of
   check_latest_sent on fuzz_transport.asan-ubsan (41113a03c82f) at 0x848bc = transportb_sigma TB_check_latest_sent
   (788 bytes, frame 160).

   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx over lib/B/TransportGB.v G_HARNESS_B, no out
   cell) from the entry to the return. The code runs as the five footprint runs of check_latest_sent_seg_runs*.v,
   each carried into SRr by lib/B/Prog/TransportFevt.v decode_run (check_latest_sent_seg_cj.v cls_chain joins a run
   to the state the last one ended in); the journal is carried across each run by cls_jexec (every byte a run writes
   is a byte of its frame, a byte of G or the caller's int at dp).
     entry (0x848bc): to the epilogue when len = 0, else to the loop head with pos = 0;
     each round (clw_loop, an induction on latest_sent_loop's fuel), with TWO call cuts:
       pre (0x84974 .. the `jal` at 0x84998), the call of tagged_of (cls_tagged: its leaf statement at the walk's
         journal, through gx_call_leaf and the leaf bridge), mid (0x8499c .. the `jal` at 0x849f0), the call of the
         bcmp wrapper (cls_bcmp: abcmp_realizes at the walk's journal; its result is 0 because the model's bytes
         agree), post (0x849f4 .. the next loop head, or the epilogue);
     epilogue (0x84b4c) to the return, and the post (clw_close).
   Across each call the view of every byte outside the callee's window below the frame is kept (cls_mem_call,
   cls_cells_call). The constant-pool word 0x10338 the entry loads is read from trans_rom_view_rd (cls_kw_of_rom).
   The post's kept bytes (acall_kept_g over cls_wr dp) come from clw_kept (every byte outside the call's window,
   outside cls_wr dp and outside g_cmd's payload keeps its view) and clw_agree (the bytes of g_cmd's payload that are
   not an st field keep their world value). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0s YK0o YM05 YK04 YA0i YA0n YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Frame Cells Step ExecF Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBAddr DgnTransportBImg DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBLeafb TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit LeafCgGlue LeafCgFacts AsanKA
  tagged_of_c tagged_of_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_latest_sent_seg_model.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_latest_sent_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_latest_sent_seg_runs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_latest_sent_seg_runs_entry
  check_latest_sent_seg_runs_pre check_latest_sent_seg_runs_post.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_latest_sent_seg_cj.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module FCW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module LCW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module LTO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_cg.
Module TOW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* the entry, the return addresses of the two calls, and the callees, as the listing layer names them *)
Lemma clw_entry_at : transportb_sigma TB_check_latest_sent = 542908.
Proof. reflexivity. Qed.
Lemma clw_bcmp_at : transportb_sigma TB___interceptor_trampoline_bcmp = 273716.
Proof. reflexivity. Qed.
Lemma clw_tag_at : TOW.TAGGED_OF = 542368.
Proof. reflexivity. Qed.

(* A register of a register map equivalent to a literal mkR map. *)
Ltac clw_reg HX := rewrite (decode_getr_xeqv _ _ HX); reflexivity.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HSC : trans_cls_cells B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS_B.
Hypothesis LEAF : forall fx' : YK11.FPState, @transport_leaf_at rc B (@LTO.transport_tagged_of_cg) fx'.
Hypothesis HBC : forall fx' : YK11.FPState,
  @abcmp_realizes fx' rc tfibsegs B (transportb_sigma TB___interceptor_trampoline_bcmp).
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (bp len dp disp : Z) (body Bw Bw' : list byte).
Hypothesis HJ : @W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
  own lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 bp.
Hypothesis H11 : YK11.getr regs 11 = w64 len.
Hypothesis H12 : YK11.getr regs 12 = w64 dp.
Hypothesis Hsp16 : spZ regs mod 16 = 0.
Hypothesis Hlo : sp0 - STK <= spZ regs - CLS_STK.
Hypothesis Hhi : spZ regs <= sp0.
Hypothesis Hbp : 0 < bp.
Hypothesis Hlen : Z.of_nat (length body) = len.
Hypothesis HG8 : garr8 tfibsegs (mrestrict (w_H W) memc) bp (TW.zs body).
Hypothesis HSRC : trans_src_ok B lyc Sc W memc bp len.
Hypothesis HOW : decode_off_win regs CLS_STK bp len.
Hypothesis HBD : forall x, bp <= x < bp + len -> ~ cls_wr dp x.
Hypothesis Hdp4 : dp mod 4 = 0.
Hypothesis HTWR : transport_twr_ok_g tfibsegs B TG.G_HARNESS_B STK sp0 FP ly S lyc Sc own W memc (spZ regs) dp 4.
Hypothesis HDR : decode_rd_ok W memc dp 4.
Hypothesis HDOW : decode_off_win regs CLS_STK dp 4.
Hypothesis HDG : forall x, dp <= x < dp + 4 -> ~ inG TG.G_HARNESS_B x.
Hypothesis HROM : trans_rom_view_rd W memc.
Hypothesis HTW : tw_at TMAP_B (aview tfibsegs (w_H W) memc) Bw.
Hypothesis HM : TC.check_latest_sent_m Bw body len = Some (Bw', disp).
Hypothesis HINV : forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING ->
  TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX.
Hypothesis Hev : st_nev S + k + CLS_EV <= EV_MAX.

Local Abbreviation spv := (spZ regs - 160).
Local Abbreviation slo := (spZ regs - CLS_STK).
Local Abbreviation RNGW := (LCW.RNG_W (world tfibsegs) (@w_H tfibsegs) W).
Local Abbreviation ra0 := (YK11.getr regs (Z_to_bv 5 1)).
Local Abbreviation gp0 := (YK11.getr regs (Z_to_bv 5 3)).
Local Abbreviation tp0 := (YK11.getr regs (Z_to_bv 5 4)).
Local Abbreviation s00 := (YK11.getr regs (Z_to_bv 5 8)).
Local Abbreviation s10 := (YK11.getr regs (Z_to_bv 5 9)).
Local Abbreviation s20 := (YK11.getr regs (Z_to_bv 5 18)).
Local Abbreviation s30 := (YK11.getr regs (Z_to_bv 5 19)).
Local Abbreviation s40 := (YK11.getr regs (Z_to_bv 5 20)).
Local Abbreviation s50 := (YK11.getr regs (Z_to_bv 5 21)).
Local Abbreviation s60 := (YK11.getr regs (Z_to_bv 5 22)).
Local Abbreviation s70 := (YK11.getr regs (Z_to_bv 5 23)).
Local Abbreviation s80 := (YK11.getr regs (Z_to_bv 5 24)).
Local Abbreviation s90 := (YK11.getr regs (Z_to_bv 5 25)).
Local Abbreviation s100 := (YK11.getr regs (Z_to_bv 5 26)).
Local Abbreviation s110 := (YK11.getr regs (Z_to_bv 5 27)).

(* ---- the post, the journal, and the invariant of every cut ---- *)

Definition clw_X : bvmap 5 word -> world tfibsegs -> (word -> option byte) -> Prop :=
  fun regs2 W2 mem2 => tw_at TMAP_B (aview tfibsegs (w_H W2) mem2) Bw' /\
                       garr8 tfibsegs (mrestrict (w_H W2) mem2) dp (TW.zs (TW.put 4 disp)).

Definition clw_post : world tfibsegs -> config -> Prop :=
  @transport_cg_post_out fx rc tfib_sink_head tfibsegs B MT TG.G_HARNESS_B [(dp, 4)] STK sp0 FP ly S W0 mem0 md0 own
    lyc Sc W memc k regs CLS_STK CLS_EV 0 (cls_wr dp) clw_X.

Definition clw_J (m : word -> option byte) (md : Model) : Prop :=
  @W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    lyc Sc W m md k.

(* every byte outside the call's window, outside the bytes the call may store and outside g_cmd's payload keeps the
   view it had at the call *)
Definition clw_kept (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < spZ regs) -> ~ cls_wr dp a -> ~ (6180992 <= a < 6180992 + 40960) ->
    aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) memc a.

Definition clw_grow (m : word -> option byte) : Prop :=
  forall a, apresent (w_H W) memc a -> apresent (w_H W) m a.

(* the bytes of g_cmd's payload that are not an st field hold their value at the call *)
Definition clw_agree (Bc : list byte) : Prop :=
  forall j i, 0 <= j < 1024 -> 4 <= i < 40 ->
    TW.u_at Bc (TW.OFF_g_cmd + 40 * j + i) 1 = TW.u_at Bw (TW.OFF_g_cmd + 40 * j + i) 1.

Definition clw_inv (m : word -> option byte) (md : Model) (Bc : list byte) (dispc : Z) : Prop :=
  clw_J m md /\ clw_kept m /\ clw_grow m /\ cls_mem m Bc body dp bp len (Z_to_bv 64 dispc) /\
  Z.of_nat (length Bc) = TW.W_LEN /\ cls_inv_c Bc /\ clw_agree Bc.

Definition clw_fr (m : word -> option byte) (j0 : list byte) : Prop :=
  Step.rw_cells rsegs m spv (cls_fr j0 dp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110).

Definition clw_fre (m : word -> option byte) (j : list byte) : Prop :=
  Step.rw_cells rsegs m spv (cls_fr_e j ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110).

(* ---- the facts of the entry state ---- *)

(* helpers of the entry facts (GlueFacts) *)

(* the donor journal inside the G journal at the call (TransportGCg.v gx_open, read off ajournal_gx directly) *)
Lemma clw_jopen : exists memS,
  @ajournal rc tfib_sink_head tfibsegs B STK sp0 FP ly S W0 memS md0 own lyc Sc W memc mdc k.
Proof.
  pose proof HJ as HJ'. destruct HJ' as (_ & _ & (memS & HJi & _) & _).
  rewrite !Z.add_0_r in HJi. exists memS. exact HJi.
Qed.

Lemma clw_AR : @AR rc tfibsegs B lyc Sc W memc mdc.
Proof. destruct clw_jopen as (memS & HJi). exact (proj1 HJi). Qed.

(* the journal's stack window (astk_ok) and the presence of its bytes *)
Lemma clw_stkf : YM05.alloc_ceiling <= sp0 - STK /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ 0 <= STK /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a).
Proof.
  destruct clw_jopen as (memS & HJi).
  destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [exact Hstk0 | exact Hpres].
Qed.

Lemma clw_cstk : CLS_STK = 8352.
Proof. reflexivity. Qed.

Lemma clw_ceil : 140735332483072 <= YM05.alloc_ceiling.
Proof. pose proof (@YM05.alloc_ceiling_val rc) as [[H1 _] _]. exact H1. Qed.

(* a byte the image view shows is not hidden *)
Lemma clw_vis_of : forall a, aview tfibsegs (w_H W) memc a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros a H. destruct (aview tfibsegs (w_H W) memc a) as [v|] eqn:E.
  - exact (decode_leafb_aview_vis W memc a v E).
  - exfalso. exact (H eq_refl).
Qed.

(* every range of G_HARNESS_B is non-empty *)
Lemma clw_G_pos : forall b n, In (b, n) TG.G_HARNESS_B -> 0 < n.
Proof.
  assert (HF : forallb (fun r => 0 <? snd r) TG.G_HARNESS_B = true) by reflexivity.
  intros b n H. rewrite forallb_forall in HF. specialize (HF (b, n) H). cbn [snd] in HF.
  apply Z.ltb_lt. exact HF.
Qed.

(* the caller's int at dp: in application memory below 2^47, addressable, visible with its shadow bytes *)
Lemma clw_dp : 0 <= dp /\ dp + 4 <= 2 ^ 47 /\
  FCW.addressable memc dp 4 /\ (forall i, 0 <= i < 4 -> w_H W (Z_to_bv 64 (FCW.shadow_addr (dp + i))) = false) /\
  (forall i, 0 <= i < 4 -> w_H W (Z_to_bv 64 (dp + i)) = false).
Proof.
  pose proof HDR as (Hv & Rra & _ & Ham & H0 & H63).
  destruct (decode_addressable_of (w_H W) memc dp 4 Rra Ham H0 ltac:(lia)) as [HA HS].
  split; [exact H0|]. split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia|].
  split; [exact HA|]. split; [exact HS|].
  intros i Hi. apply clw_vis_of. apply Hv. lia.
Qed.

(* the body lies below 2^47: a heap block of the caller ends at or below alloc_ceiling (AR_blocks_law), every other
   placement of trans_src_ok carries decode_rd_ok's amem_range *)
Lemma clw_bp : 0 < bp /\ 0 <= len /\ bp + len <= 2 ^ 47.
Proof.
  assert (L0 : 0 <= len) by (rewrite <- Hlen; lia).
  split; [exact Hbp|]. split; [exact L0|].
  pose proof HSRC as HS.
  destruct HS as [(bA & nA & Hin & B1 & B2) | (_ & (_ & _ & _ & Ham & _ & _))].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA clw_AR Hin) as (_ & _ & Hce & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq]. pose proof (@YM05.alloc_ceiling_lt rc). lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia.
Qed.

(* the shadow byte of every byte of a zero-shadow range of the record is visible (decode_zshadow_rd at its granule) *)
Lemma clw_zsh_vis : forall lo n i, decode_zshadow_at B lo (lo + n) -> lo mod 8 = 0 -> n mod 8 = 0 -> 0 <= lo ->
  0 <= i < n -> w_H W (Z_to_bv 64 (FCW.shadow_addr (lo + i))) = false.
Proof.
  intros lo n i HZ Hl8 Hn H0 Hi.
  assert (E : FCW.shadow_addr ((lo + i) / 8 * 8) = FCW.shadow_addr (lo + i)).
  { unfold FCW.shadow_addr. rewrite Z.div_mul by lia. reflexivity. }
  rewrite <- E.
  apply (decode_leafb_aview_vis W memc _ 0).
  apply (decode_zshadow_rd B lyc Sc W memc mdc lo (lo + n) ((lo + i) / 8 * 8) clw_AR);
    [apply Z_mod_mult | | | exact HZ];
    clear E; Z.div_mod_to_equations; lia.
Qed.

(* a check over [base, base + R * Q) as Q blocks of R bytes: the block base is computed once per block, so vm_compute
   converts no large unary nat (gx_bytes' Z.of_nat over seq 0 n is quadratic in n) *)
Lemma clw_fb2 : forall (f : Z -> bool) (base : Z) (R Q : nat),
  forallb (fun q => let z := base + Z.of_nat R * Z.of_nat q in forallb (fun r => f (z + Z.of_nat r)) (seq 0 R))
    (seq 0 Q) = true ->
  forall a, base <= a < base + Z.of_nat R * Z.of_nat Q -> f a = true.
Proof.
  intros f base R Q H a Ha.
  assert (HR : 0 < Z.of_nat R) by nia.
  assert (Hq : 0 <= (a - base) / Z.of_nat R < Z.of_nat Q).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  pose proof (Z.div_mod (a - base) (Z.of_nat R) ltac:(lia)) as Ed.
  pose proof (Z.mod_pos_bound (a - base) (Z.of_nat R) HR) as Bd.
  rewrite forallb_forall in H.
  specialize (H (Z.to_nat ((a - base) / Z.of_nat R)) ltac:(apply in_seq; lia)).
  cbv beta zeta in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat ((a - base) mod Z.of_nat R)) ltac:(apply in_seq; lia)).
  cbv beta in H. rewrite !Z2Nat.id in H by lia.
  replace a with (base + Z.of_nat R * ((a - base) / Z.of_nat R) + (a - base) mod Z.of_nat R) by lia.
  exact H.
Qed.

(* the bytes of g_cmd's and g_q's payloads and of g_nq lie in a writable loaded segment, which holds a byte for each
   (wview at the empty memory; decided by vm_compute, the wview half of lib/A/Prog/TransportGCg.v gx_rwb) *)
Lemma clw_g_wb : forall a,
  (6180992 <= a < 6180992 + 40960) \/ (6232192 <= a < 6232192 + 4096) \/ (6157792 <= a < 6157792 + 4) ->
  match wview tfibsegs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end = true.
Proof.
  intros a [Ha | [Ha | Ha]].
  - apply (clw_fb2 (fun a => match wview tfibsegs (fun _ => None) (Z_to_bv 64 a) with
                             | Some _ => true | None => false end) 6180992 64 640);
      [vm_compute; reflexivity | change (Z.of_nat 64 * Z.of_nat 640) with 40960; lia].
  - apply (clw_fb2 (fun a => match wview tfibsegs (fun _ => None) (Z_to_bv 64 a) with
                             | Some _ => true | None => false end) 6232192 64 64);
      [vm_compute; reflexivity | change (Z.of_nat 64 * Z.of_nat 64) with 4096; lia].
  - apply (clw_fb2 (fun a => match wview tfibsegs (fun _ => None) (Z_to_bv 64 a) with
                             | Some _ => true | None => false end) 6157792 4 1);
      [vm_compute; reflexivity | change (Z.of_nat 4 * Z.of_nat 1) with 4; lia].
Qed.

Lemma clw_wok_g : forall (m : word -> option byte) a,
  (6180992 <= a < 6180992 + 40960) \/ (6232192 <= a < 6232192 + 4096) \/ (6157792 <= a < 6157792 + 4) ->
  wview rsegs m (wa a) <> None.
Proof.
  intros m a Ha. pose proof (clw_g_wb a Ha) as E.
  destruct (m (wa a)) as [b|] eqn:Em.
  - exact (decode_wview_some m _ b Em).
  - assert (EE : wview tfibsegs m (wa a) = wview tfibsegs (fun _ => None) (Z_to_bv 64 a))
      by exact (gx_wview_none tfibsegs m (wa a) Em).
    change (wview tfibsegs m (wa a) <> None). rewrite EE. exact (gx_rw_some _ E).
Qed.

(* end of the helpers of the entry facts *)

Lemma clw_stack : YM05.alloc_ceiling <= sp0 - STK /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ 0 <= STK /\
  CLS_STK = 8352 /\ (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a).
Proof.
  pose proof clw_stkf as (Hc & H47 & Hal & Hs0 & Hpres).
  split; [exact Hc|]. split; [exact H47|]. split; [exact Hal|]. split; [exact Hs0|].
  split; [exact clw_cstk | exact Hpres].
Qed.

Lemma clw_bounds : cls_bounds spv dp bp len.
Proof.
  pose proof clw_stkf as (Hc & H47 & _ & Hs0 & _). pose proof clw_cstk as HCS. pose proof clw_ceil as Hce.
  pose proof clw_dp as (D0 & D47 & _). pose proof clw_bp as (B0 & L0 & BL).
  unfold cls_bounds. repeat split; lia.
Qed.

Lemma clw_app_sp : cls_app spv 160.
Proof.
  pose proof clw_stkf as (Hc & H47 & _). pose proof clw_cstk as HCS. pose proof clw_ceil as Hce.
  unfold cls_app, FCW.LOWMEM_END, FCW.HIGHMEM_BEG, FCW.APPMEM_END. right. lia.
Qed.

Lemma clw_app_dp : cls_app dp 4.
Proof.
  pose proof HDR as (_ & _ & _ & Ham & H0 & _).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
  unfold cls_app, FCW.LOWMEM_END, FCW.HIGHMEM_BEG, FCW.APPMEM_END. lia.
Qed.

Lemma clw_off : cls_off spv dp bp len.
Proof.
  pose proof clw_stkf as (Hc & H47 & _ & Hs0 & Hpres). pose proof clw_cstk as HCS. pose proof clw_ceil as Hce.
  pose proof clw_dp as (D0 & D47 & _). pose proof clw_bp as (B0 & L0 & BL).
  pose proof HDOW as DW. pose proof HOW as BW. unfold decode_off_win in DW, BW.
  unfold cls_off, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI, CLS_KSENT.
  split; [right; lia|]. split; [right; lia|]. split; [right; lia|]. split; [right; lia|].
  split.
  { (* dp off the constant-pool word: a byte at dp is an awr_byte of the journal (G is excluded), so a stack byte or
       a byte of a block or a frame of the caller, which AR keeps out of the image; the pool word's bytes are image
       bytes *)
    apply (cls_disj_of_pt dp 4 66360 8); [lia | lia |].
    intros x Hx Hp.
    assert (Hi : in_img tfibsegs x).
    { replace x with (66360 + (x - 66360)) by lia. apply trans_ro_img. apply cls_ksent_ro. lia. }
    destruct (HTWR x Hx) as [(Hw & _ & _ & _) | HG]; [| exact (HDG x Hx HG)].
    destruct clw_jopen as (memS & HJi).
    destruct (awr_byte_cases tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x HJi Hw)
      as (_ & [(Hc1 & _) | [(_ & bb & nn & Hin & Hr & _) | (cid & pos & Hin & [(_ & Hr) | (Hr & _)])]]).
    - lia.
    - exact (proj2 (al_client_img _ _ LAWS lyc Sc W memc mdc x clw_AR
                      (or_introl (ex_intro _ bb (ex_intro _ nn (conj Hin Hr))))) Hi).
    - assert (Hf : In (cid, pos) (frames Sc)).
      { pose proof HJi as (_ & _ & _ & _ & _ & Hfr & _). rewrite Hfr. apply in_or_app. left. exact Hin. }
      unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
      exact (proj2 (al_client_img _ _ LAWS lyc Sc W memc mdc x clw_AR
                      (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hf Hr)))))) Hi).
    - unfold kLowMemEnd in Hr. lia. }
  split; [lia|]. split; [lia|].
  split.
  { (* dp off every range of G *)
    intros b n Hin. apply (cls_disj_of_pt dp 4 b n); [lia | exact (clw_G_pos b n Hin) |].
    intros x Hx Hb. apply (HDG x Hx). unfold inG. apply Exists_exists. exists (b, n).
    split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  split.
  { intros Hl s Hs. apply (cls_disj_of_pt bp len (6180992 + 40 * s) 4); [lia | lia |].
    intros x Hx Hc2. apply (HBD x Hx). left. exists s. split; [unfold TC.CMDS_MAX; lia |].
    unfold twb_fld, TW.A_Cmd_st, TW.OFF_g_cmd, TB_g_cmd. lia. }
  split.
  { intros Hl. apply (cls_disj_of_pt bp len 6232192 4096); [lia | lia |].
    intros x Hx Hc2. apply (HBD x Hx). right. left.
    unfold twb_fld, TW.OFF_g_q, TB_g_q, TW.SZ_g_q. lia. }
  split.
  { intros Hl. apply (cls_disj_of_pt bp len 6157792 4); [lia | lia |].
    intros x Hx Hc2. apply (HBD x Hx). right. right. left.
    unfold twb_fld, TW.OFF_g_nq, TB_g_nq, TW.SZ_g_nq. lia. }
  { intros Hl. apply (cls_disj_of_pt bp len dp 4); [lia | lia |].
    intros x Hx Hc2. apply (HBD x Hx). right. right. right. lia. }
Qed.

Lemma clw_rng : cls_rng RNGW spv dp.
Proof.
  pose proof clw_stkf as (Hc & H47 & _ & Hs0 & Hpres). pose proof clw_cstk as HCS. pose proof clw_ceil as Hce.
  pose proof clw_dp as (D0 & D47 & _ & DS & DV).
  unfold cls_rng.
  split; [apply decode_rng_vis; [lia | lia | intros i Hi; exact (proj1 (Hpres (spZ regs - 160 + i) ltac:(lia)))]|].
  split; [exact (proj1 (decode_leafb_rng_cells W))|].
  split; [exact (proj2 (decode_leafb_rng_cells W))|].
  split; [apply decode_rng_vis; [lia | lia | exact DV]|].
  split.
  { apply decode_rng_vis; [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia |].
    intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r.
    pose proof (DS 0 ltac:(lia)) as E. rewrite Z.add_0_r in E. unfold FCW.shadow_addr, FCW.ASAN_K in E. exact E. }
  split.
  { unfold CLS_KSENT. apply decode_rng_vis; [lia | lia |].
    intros i Hi. pose proof (cls_ksent_ro i Hi) as R.
    destruct (trans_ro_rd_rom_clean _ R) as [_ (b & Hb)].
    apply (decode_leafb_aview_vis W memc _ (bv_unsigned b)).
    rewrite (HROM _ R), Hb. reflexivity. }
  split.
  { apply decode_rng_vis; [lia | lia |]. intros i Hi. apply cls_vis.
    exists TW.OFF_g_cmd, TB_g_cmd, TW.SZ_g_cmd. split; [exact TMAP_B_g_cmd | unfold TB_g_cmd, TW.SZ_g_cmd; lia]. }
  split.
  { apply decode_rng_vis; [lia | lia |]. intros i Hi.
    replace (2148223504 + i) with (FCW.shadow_addr (TB_g_cmd + 8 * i))
      by (unfold FCW.shadow_addr, FCW.ASAN_K, TB_g_cmd; Z.div_mod_to_equations; lia).
    exact (clw_zsh_vis TB_g_cmd TW.SZ_g_cmd (8 * i) (proj2 HSC) eq_refl eq_refl
             ltac:(unfold TB_g_cmd; lia) ltac:(unfold TW.SZ_g_cmd; lia)). }
  split.
  { apply decode_rng_vis; [lia | lia |]. intros i Hi. apply cls_vis.
    exists TW.OFF_g_q, TB_g_q, TW.SZ_g_q. split; [exact TMAP_B_g_q | unfold TB_g_q, TW.SZ_g_q; lia]. }
  split.
  { apply decode_rng_vis; [lia | lia |]. intros i Hi.
    replace (2148229904 + i) with (FCW.shadow_addr (TB_g_q + 8 * i))
      by (unfold FCW.shadow_addr, FCW.ASAN_K, TB_g_q; Z.div_mod_to_equations; lia).
    exact (clw_zsh_vis TB_g_q TW.SZ_g_q (8 * i) (proj1 HSC) eq_refl eq_refl
             ltac:(unfold TB_g_q; lia) ltac:(unfold TW.SZ_g_q; lia)). }
  { apply decode_rng_vis; [lia | lia |]. intros i Hi. apply cls_vis.
    exists TW.OFF_g_nq, TB_g_nq, TW.SZ_g_nq. split; [exact TMAP_B_g_nq | unfold TB_g_nq, TW.SZ_g_nq; lia]. }
Qed.

(* the body's bytes and their shadow bytes are visible, the body lies in application memory below 2^47 *)
Lemma clw_body_vis : forall i, 0 <= i < len -> w_H W (Z_to_bv 64 (bp + i)) = false.
Proof.
  intros i Hi.
  assert (Hj : (Z.to_nat i < length (TW.zs body))%nat) by (unfold TW.zs; rewrite length_map; lia).
  destruct (HG8 (Z.to_nat i) Hj) as [HV _].
  specialize (HV 0%nat ltac:(lia)).
  rewrite Z2Nat.id in HV by lia. rewrite Nat2Z.inj_0, Z.add_0_r in HV.
  exact (decode_leafb_mbyte_vis W memc _ _ HV).
Qed.

Lemma clw_body_shvis : forall i, 0 <= i < len -> w_H W (Z_to_bv 64 (FCW.shadow_addr (bp + i))) = false.
Proof.
  intros i Hi.
  pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc bp len clw_AR HSRC ltac:(lia)) as (_ & Rra & _ & Ham & H0 & _).
  exact (proj2 (decode_addressable_of (w_H W) memc bp len Rra Ham H0 ltac:(lia)) i Hi).
Qed.

Lemma clw_body_rd : 0 < len -> decode_rd_ok W memc bp len.
Proof. intros Hl. exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc bp len clw_AR HSRC Hl). Qed.

(* the bytes cls_mem reads are visible, and outside the call's window *)
Lemma clw_membytes : forall a, cls_mem_bytes dp bp len a ->
  0 <= a < 2 ^ 64 /\ ~ (slo <= a < spZ regs) /\ w_H W (Z_to_bv 64 a) = false.
Proof.
  intros a Ha.
  pose proof clw_stkf as (Hc & H47 & _ & Hs0 & _). pose proof clw_cstk as HCS. pose proof clw_ceil as Hce.
  pose proof clw_dp as (D0 & D47 & _ & DS & DV). pose proof clw_bp as (B0 & L0 & BL).
  pose proof HDOW as DW. pose proof HOW as BW. unfold decode_off_win in DW, BW.
  unfold cls_mem_bytes in Ha.
  destruct Ha as [Ha | [Ha | [Ha | [(i & Hi & ->) | [(i & Hi & ->) | [(i & Hi & ->) | (i & Hi & ->)]]]]]].
  - pose proof (TMAP_B_hull a Ha) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    split; [lia|]. split; [lia|]. exact (cls_vis W a Ha).
  - split; [lia|]. split; [lia|]. replace a with (dp + (a - dp)) by lia. apply DV. lia.
  - split; [lia|]. split; [lia|]. replace a with (bp + (a - bp)) by lia. apply clw_body_vis. lia.
  - assert (E : 0 <= FCW.shadow_addr (6180992 + i) < 2147450880 + 2 ^ 44)
      by (unfold FCW.shadow_addr, FCW.ASAN_K; Z.div_mod_to_equations; lia).
    split; [lia|]. split; [lia|].
    exact (clw_zsh_vis TB_g_cmd TW.SZ_g_cmd i (proj2 HSC) eq_refl eq_refl
             ltac:(unfold TB_g_cmd; lia) ltac:(unfold TW.SZ_g_cmd; lia)).
  - assert (E : 0 <= FCW.shadow_addr (6232192 + i) < 2147450880 + 2 ^ 44)
      by (unfold FCW.shadow_addr, FCW.ASAN_K; Z.div_mod_to_equations; lia).
    split; [lia|]. split; [lia|].
    exact (clw_zsh_vis TB_g_q TW.SZ_g_q i (proj1 HSC) eq_refl eq_refl
             ltac:(unfold TB_g_q; lia) ltac:(unfold TW.SZ_g_q; lia)).
  - assert (E : 0 <= FCW.shadow_addr (dp + i) < 2147450880 + 2 ^ 44)
      by (unfold FCW.shadow_addr, FCW.ASAN_K; Z.div_mod_to_equations; lia).
    split; [lia|]. split; [lia|]. exact (DS i Hi).
  - assert (E : 0 <= FCW.shadow_addr (bp + i) < 2147450880 + 2 ^ 44)
      by (unfold FCW.shadow_addr, FCW.ASAN_K; Z.div_mod_to_equations; lia).
    split; [lia|]. split; [lia|]. exact (clw_body_shvis i Hi).
Qed.

Lemma clw_mem0 : exists v0, cls_mem memc Bw body dp bp len v0.
Proof.
  pose proof clw_dp as (D0 & D47 & DA & _ & _). pose proof clw_bp as (B0 & L0 & BL).
  assert (P4 : forall i, 0 <= i < 4 -> apresent (w_H W) memc (dp + i)).
  { intros i Hi. destruct (HTWR (dp + i) ltac:(lia)) as [(_ & Hp & _) | HG];
      [exact Hp | exfalso; exact (HDG (dp + i) ltac:(lia) HG)]. }
  destruct (cls_c4_present (w_H W) memc dp D0 ltac:(lia) P4) as (v & Hv).
  exists v. unfold cls_mem.
  split; [exact (cls_tw_raw W memc Bw HTW)|].
  split; [exact Hv|].
  split.
  { unfold cls_body. apply (decode_garr8_bytes (w_H W) memc bp body); [lia | lia | | exact HG8].
    intros j Hj. apply clw_body_vis. lia. }
  split.
  { destruct (decode_zshadow_ra B lyc Sc W memc mdc TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd) 6180992 40960 clw_AR
                (proj2 HSC) ltac:(lia) ltac:(unfold TB_g_cmd; apply Z.leb_le; reflexivity)
                ltac:(unfold TB_g_cmd, TW.SZ_g_cmd; apply Z.leb_le; reflexivity)) as [Rra _].
    exact (proj1 (decode_addressable_of (w_H W) memc 6180992 40960 Rra
                    ltac:(unfold amem_range, kLowMemEnd; lia) ltac:(lia) ltac:(lia))). }
  split.
  { destruct (decode_zshadow_ra B lyc Sc W memc mdc TB_g_q (TB_g_q + TW.SZ_g_q) 6232192 4096 clw_AR
                (proj1 HSC) ltac:(lia) ltac:(unfold TB_g_q; apply Z.leb_le; reflexivity)
                ltac:(unfold TB_g_q, TW.SZ_g_q; apply Z.leb_le; reflexivity)) as [Rra _].
    exact (proj1 (decode_addressable_of (w_H W) memc 6232192 4096 Rra
                    ltac:(unfold amem_range, kLowMemEnd; lia) ltac:(lia) ltac:(lia))). }
  split; [exact DA|].
  split.
  { destruct (Z.eq_dec len 0) as [L | L].
    - rewrite L. unfold FCW.addressable.
      split; [lia|]. split; [lia|]. split; [unfold FCW.APPMEM_END; lia | intros i Hi; lia].
    - pose proof (clw_body_rd ltac:(lia)) as (_ & Rra & _ & Ham & H0 & _).
      exact (proj1 (decode_addressable_of (w_H W) memc bp len Rra Ham H0 L0)). }
  intros a Ha. unfold cls_wrange in Ha.
  destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - apply clw_wok_g. left. exact Ha.
  - apply clw_wok_g. right. left. exact Ha.
  - apply clw_wok_g. right. right. exact Ha.
  - destruct (P4 (a - dp) ltac:(lia)) as [_ (b & Hb)].
    replace (dp + (a - dp)) with a in Hb by lia. exact (decode_wview_some memc _ b Hb).
Qed.

Lemma clw_cells0 : FCW.asan_cells memc.
Proof. exact (decode_leafb_asan_cells B HCELLS lyc Sc W memc mdc clw_AR). Qed.

Lemma clw_kw0 : cls_kw memc.
Proof. unfold cls_kw, CLS_KSENT, CLS_KVAL. exact (cls_kw_of_rom W memc HROM). Qed.

Lemma clw_stk0 : Frame.stk rsegs memc slo (spZ regs).
Proof.
  pose proof clw_stkf as (Hc & H47 & _ & Hs0 & Hpres). pose proof clw_cstk as HCS. pose proof clw_ceil as Hce.
  apply (decode_stk_present (w_H W) memc); [lia | lia |]. intros a Ha. apply Hpres. lia.
Qed.

Lemma clw_inv0 : forall v0, cls_mem memc Bw body dp bp len v0 -> clw_J memc mdc /\ clw_kept memc /\ clw_grow memc /\
  Z.of_nat (length Bw) = TW.W_LEN /\ cls_inv_c Bw /\ clw_agree Bw.
Proof.
  intros v0 _. split; [exact HJ|]. split; [intros a _ _ _ _; reflexivity|]. split; [intros a Ha; exact Ha|].
  split; [rewrite (tw_len TMAP_B _ Bw HTW); apply Z2Nat.id; unfold TW.W_LEN; lia|].
  split; [exact (cls_inv_to_c Bw HINV)|]. intros j i _ _. reflexivity.
Qed.

(* ---- the steps: a run of the walk's own code, a call, a step with no store ---- *)

(* helpers of the steps, the close and the epilogue (GlueSteps) *)

(* the journal's window, its placement and its presence at any memory the journal reaches *)
Lemma clws_J_win : forall (m : word -> option byte) md, clw_J m md ->
  @AR rc tfibsegs B lyc Sc W m md /\ YM05.alloc_ceiling <= sp0 - STK /\ sp0 <= 2 ^ 47 /\ 0 <= STK /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) m a).
Proof.
  intros m md HJm.
  destruct HJm as (HSTK & _ & (memS & HJi & _) & _).
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  split; [exact HAR|]. split; [lia|]. split; [lia|]. split; [exact HSTK|].
  intros a Ha. apply Hpres. lia.
Qed.

Lemma clws_uns : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
  intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Ha.
Qed.

(* the written window of a run: its five ranges *)
Lemma clws_W_cases : forall a, ~ Frame.outside (cls_W spv dp) a ->
  (spv <= a < spv + 160) \/ (6180992 <= a < 6180992 + 40960) \/ (6232192 <= a < 6232192 + 4096) \/
  (6157792 <= a < 6157796) \/ (dp <= a < dp + 4).
Proof. intros a H. unfold cls_W in H. cbn [Frame.outside] in H. lia. Qed.

Lemma clws_out_nn : forall a, ~ ~ Frame.outside (cls_W spv dp) a -> Frame.outside (cls_W spv dp) a.
Proof. intros a H. unfold cls_W in *. cbn [Frame.outside] in *. lia. Qed.

(* a byte off the frame, off cls_wr dp and off g_cmd's payload is outside the run's window *)
Lemma clws_out_of : forall a, ~ (spv <= a < spv + 160) -> ~ cls_wr dp a -> ~ (6180992 <= a < 6180992 + 40960) ->
  Frame.outside (cls_W spv dp) a.
Proof.
  intros a Hf Hw Hc.
  assert (Hq : ~ (6232192 <= a < 6232192 + 4096)).
  { intros Hx. apply Hw. unfold cls_wr. right; left. unfold twb_fld, TW.OFF_g_q, TB_g_q, TW.SZ_g_q. lia. }
  assert (Hn : ~ (6157792 <= a < 6157796)).
  { intros Hx. apply Hw. unfold cls_wr. right; right; left. unfold twb_fld, TW.OFF_g_nq, TB_g_nq, TW.SZ_g_nq. lia. }
  assert (Hd : ~ (dp <= a < dp + 4)).
  { intros Hx. apply Hw. unfold cls_wr. right; right; right. exact Hx. }
  unfold cls_W. cbn [Frame.outside]. lia.
Qed.

(* the payloads of g_cmd, g_q and g_nq are bytes of G *)
Lemma clws_inG_w : forall a, (6180992 <= a < 6180992 + 40960) \/ (6232192 <= a < 6232192 + 4096) \/
  (6157792 <= a < 6157796) -> inG TG.G_HARNESS_B a.
Proof.
  intros a H. unfold inG. apply Exists_exists.
  destruct H as [H | [H | H]].
  - exists (TB_g_cmd, TW.SZ_g_cmd). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_cmd)|].
    unfold in_zr, TB_g_cmd, TW.SZ_g_cmd. cbn [fst snd]. lia.
  - exists (TB_g_q, TW.SZ_g_q). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_q)|].
    unfold in_zr, TB_g_q, TW.SZ_g_q. cbn [fst snd]. lia.
  - exists (TB_g_nq, TW.SZ_g_nq). split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_nq)|].
    unfold in_zr, TB_g_nq, TW.SZ_g_nq. cbn [fst snd]. lia.
Qed.

(* a byte of g_cmd's payload read in two worlds that agree on it *)
Lemma clws_cmd_eq : forall (rd rd' : Z -> option Z) (Bc Bc' : list byte) a,
  tw_at TMAP_B rd Bc -> tw_at TMAP_B rd' Bc' -> 6180992 <= a < 6180992 + 40960 ->
  TW.u_at Bc' (TW.OFF_g_cmd + (a - 6180992)) 1 = TW.u_at Bc (TW.OFF_g_cmd + (a - 6180992)) 1 ->
  rd' a = rd a.
Proof.
  intros rd rd' Bc Bc' a H H' Ha E.
  assert (Ea : a = TB_g_cmd + (a - 6180992) + Z.of_nat 0) by (unfold TB_g_cmd; lia).
  rewrite Ea.
  rewrite (tw_read TMAP_B rd' Bc' TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (a - 6180992) 1 0 TMAP_B_ok H' TMAP_B_g_cmd)
    by (unfold TW.SZ_g_cmd; lia).
  rewrite (tw_read TMAP_B rd Bc TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (a - 6180992) 1 0 TMAP_B_ok H TMAP_B_g_cmd)
    by (unfold TW.SZ_g_cmd; lia).
  rewrite E. reflexivity.
Qed.

(* the 4 bytes of a C4 cell of v are the world's put 4 v *)
Lemma clws_le4_put : forall v, le4 (Z_to_bv 64 v) = TW.put 4 v.
Proof.
  intros v. unfold le4, TW.put. rewrite unsigned_lit_wrap.
  rewrite <- (Z_to_le_bytes_mod 4 (v mod 2 ^ 64) 32) by (cbn; lia).
  rewrite cls_mod64_32. rewrite (Z_to_le_bytes_mod 4 v 32) by (cbn; lia). reflexivity.
Qed.

(* end of the helpers of the steps *)

Lemma clw_run_step : forall (m m' : word -> option byte) md md',
  clw_J m md -> clw_kept m -> clw_grow m ->
  Frame.munch (cls_W spv dp) m m' -> YK1b.mem_grows m m' -> same_but_materialized md md' ->
  clw_J m' md' /\ clw_kept m' /\ clw_grow m'.
Proof.
  intros m m' md md' HJm HK HG MU MG Hs.
  pose proof (clws_J_win m md HJm) as (_ & Hce & H47 & HSTK & Hwin).
  assert (HCS : CLS_STK = 8352) by reflexivity.
  split; [|split].
  - apply (cls_jexec B LAWS HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m m' md md' k
             (fun a => ~ Frame.outside (cls_W spv dp) a) HJm).
    + intros z Hz. apply MU. exact (clws_out_nn _ Hz).
    + exact MG.
    + exact Hs.
    + intros a Ha. destruct (clws_W_cases a Ha) as [Hf | [Hc | [Hq | [Hn | Hd]]]].
      * left. split; [unfold awr_byte; left; lia | apply Hwin; lia].
      * right. apply clws_inG_w. left. exact Hc.
      * right. apply clws_inG_w. right; left. exact Hq.
      * right. apply clws_inG_w. right; right. exact Hn.
      * destruct (HTWR a Hd) as [(Haw & Hp & _ & _) | HGa].
        -- left. split; [exact Haw | exact (HG a Hp)].
        -- exfalso. exact (HDG a Hd HGa).
  - intros a Ha Hw Hcw Hcmd. rewrite <- (HK a Ha Hw Hcw Hcmd).
    apply aview_eq_of.
    assert (E : m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { apply MU. rewrite (clws_uns a Ha). apply clws_out_of; [lia | exact Hcw | exact Hcmd]. }
    unfold mrestrict. rewrite E. reflexivity.
  - intros a Ha. destruct (HG a Ha) as [Hh [b Hb]]. split; [exact Hh|].
    destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
    exfalso. apply (MG (Z_to_bv 64 a)); [rewrite Hb; discriminate | exact E].
Qed.

Lemma clw_sbm_step : forall (m : word -> option byte) md md',
  clw_J m md -> same_but_materialized md md' -> clw_J m md'.
Proof.
  intros m md md' HJm Hs.
  apply (cls_jexec B LAWS HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m m md md' k (fun _ => False) HJm).
  - intros z _. reflexivity.
  - intros z Hz. exact Hz.
  - exact Hs.
  - intros a [].
Qed.

Lemma clw_call_step : forall (m m2 : word -> option byte) (lo : Z),
  slo <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < spv) -> aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m2 a) ->
  clw_kept m -> clw_grow m -> clw_kept m2 /\ clw_grow m2.
Proof.
  intros m m2 lo Hlo' KV GR HK HG. split.
  - intros a Ha Hw Hcw Hcmd. rewrite (KV a Ha) by lia. exact (HK a Ha Hw Hcw Hcmd).
  - intros a Ha. exact (GR a (HG a Ha)).
Qed.

(* the frame across a call: its bytes are present (the journal's window) and outside the callee's window *)
Lemma clw_fr_call : forall (m m2 : word -> option byte) md md2 (lo : Z) (cs : list Cells.cell),
  slo <= lo -> clw_J m md -> clw_J m2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < spv) -> aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m a) ->
  Z.of_nat (Cells.cells_size cs) = 160 ->
  Step.rw_cells rsegs m spv cs -> Step.rw_cells rsegs m2 spv cs.
Proof.
  intros m m2 md md2 lo cs Hlo' HJ1 HJ2 KV Hsz HC.
  pose proof (clws_J_win m md HJ1) as (_ & Hce & H47 & HSTK & Hw1).
  pose proof (clws_J_win m2 md2 HJ2) as (_ & _ & _ & _ & Hw2).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  assert (HCS : CLS_STK = 8352) by reflexivity.
  apply (cls_cells_call W m m2 spv cs HC).
  intros i Hi. rewrite Hsz in Hi.
  split; [apply Hw1; lia|]. split; [apply Hw2; lia|].
  apply KV; lia.
Qed.

(* ---- the close ---- *)

Lemma clw_close : forall (regsF : bvmap 5 word) (mF : word -> option byte) (mdF : Model),
  clw_J mF mdF -> clw_kept mF -> clw_grow mF -> cls_mem mF Bw' body dp bp len (Z_to_bv 64 disp) -> clw_agree Bw' ->
  aregs_preserved regs regsF ->
  clw_post W (mkCfg (@YK11.mkst fx regsF (YK11.getr regs 1) mF (YK11.seg_rom tfibsegs)) mdF).
Proof.
  intros regsF mF mdF HJF HK HG HMF HA HP.
  pose proof (clws_J_win memc mdc HJ) as (HAR & Hce & H47 & HSTK & Hwc).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  assert (HCS : CLS_STK = 8352) by reflexivity.
  pose proof HMF as (HTWF & HC4 & _).
  pose proof (cls_tw_av W mF Bw' HTWF) as HTWA.
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < spZ regs) -> ~ cls_wr dp a ->
    aview tfibsegs (w_H W) mF a = aview tfibsegs (w_H W) memc a).
  { intros a Ha Hw Hcw.
    destruct (Z_lt_le_dec a 6180992) as [L1|L1]; [apply HK; [exact Ha | exact Hw | exact Hcw | lia]|].
    destruct (Z_lt_le_dec a (6180992 + 40960)) as [L2|L2]; [|apply HK; [exact Ha | exact Hw | exact Hcw | lia]].
    pose proof (Z.div_mod (a - 6180992) 40 ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (a - 6180992) 40 ltac:(lia)) as MB.
    assert (J : 0 <= (a - 6180992) / 40 < 1024).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    destruct (Z_lt_le_dec ((a - 6180992) mod 40) 4) as [I|I].
    - exfalso. apply Hcw. unfold cls_wr. left. exists ((a - 6180992) / 40).
      split; [unfold TC.CMDS_MAX; lia|].
      unfold twb_fld, TW.A_Cmd_st, TW.OFF_g_cmd, TB_g_cmd. lia.
    - apply (clws_cmd_eq (aview tfibsegs (w_H W) memc) (aview tfibsegs (w_H W) mF) Bw Bw' a HTW HTWA
               ltac:(lia)).
      pose proof (HA ((a - 6180992) / 40) ((a - 6180992) mod 40) J ltac:(lia)) as E.
      replace (TW.OFF_g_cmd + (a - 6180992))
        with (TW.OFF_g_cmd + 40 * ((a - 6180992) / 40) + (a - 6180992) mod 40) by lia.
      exact E. }
  unfold clw_post, transport_cg_post_out.
  exists lyc, Sc, regsF, mF, mdF, 0.
  split; [reflexivity|].
  split; [unfold CLS_EV; lia|].
  split; [rewrite Z.add_0_r; exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (cls_close_kept B LAWS HGX lyc Sc W memc mdc mF dp slo (spZ regs) HAR).
    - lia.
    - lia.
    - intros a Ha. apply Hwc. lia.
    - exact KA.
    - exact HG. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  split; [exact HTWA|].
  destruct HC4 as [[_ Hb] _]. cbn [Cells.cells_bytes Cells.cbytes] in Hb. rewrite app_nil_r in Hb.
  unfold TW.zs. apply (decode_bytes_garr8 (w_H W) mF dp (TW.put 4 disp)); [|rewrite <- clws_le4_put; exact Hb].
  intros j Hj. rewrite TWorldLemmas.length_put in Hj.
  destruct (HTWR (dp + Z.of_nat j) ltac:(lia)) as [(_ & (Hh & _) & _ & _) | HGa]; [exact Hh|].
  exfalso. exact (HDG (dp + Z.of_nat j) ltac:(lia) HGa).
Qed.

(* ---- the epilogue ---- *)

Lemma clw_epi : forall (m : word -> option byte) (md : Model) (ms : machine_state) (j : list byte)
    (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
     y28 y29 y30 y31 : word),
  clw_J m md -> clw_kept m -> clw_grow m -> cls_mem m Bw' body dp bp len (Z_to_bv 64 disp) -> clw_agree Bw' ->
  length j = 56%nat -> clw_fre m j ->
  Regs6ss.ms_eqv (MS (Frame.mkR y1 (Z_to_bv 64 spv) gp0 tp0 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                          y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                      (@YK11.fp_regs fx) (Z_to_bv 64 543564) (@YK11.fp_csr fx) None m (YK11.seg_rom rsegs)) ms ->
  SRr tfibsegs W (mkCfg ms md) clw_post.
Proof.
  intros m md ms j y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
    y28 y29 y30 y31 HJm HK HG HMF HA Hj HFR HE.
  pose proof (clws_J_win m md HJm) as (_ & Hce & H47 & HSTK & Hwin).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  assert (HCS : CLS_STK = 8352) by reflexivity.
  apply (@cls_chain fx W _ 543564 m md ms
           (fun ms1 => ms1 = MS (Frame.mkR ra0 (Z_to_bv 64 (spv + 160)) gp0 tp0 y5 y6 y7 s00 s10
                                  y10 y11 y12 y13 y14 y15 y16 y17 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110
                                  y28 y29 y30 y31)
                                (@YK11.fp_regs fx) (ret_pc ra0) (@YK11.fp_csr fx) None m (YK11.seg_rom rsegs))
           clw_post HE).
  - apply (cls_run_epi RNGW _ m (@YK11.fp_regs fx) (@YK11.fp_csr fx) spv j
             ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110
             y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
             gp0 tp0 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31).
    + lia.
    + lia.
    + exact HFR.
    + apply decode_rng_vis; [lia | lia |].
      intros i Hi. destruct (Hwin (spv + i) ltac:(lia)) as [Hh _]. exact Hh.
    + apply ExecF.evtF_done. reflexivity.
  - intros ms1 ms3 md'' -> HE3 _ Hs.
    destruct (@decode_eqv_mkst fx _ _ _ _ HE3) as (R'' & -> & HX).
    rewrite (LeafCgFacts.ret_ok_stmt_YK0s (YK11.getr regs (Z_to_bv 5 1)) Hra).
    apply SRr_ret.
    apply (clw_close R'' m md'' (clw_sbm_step m md md'' HJm Hs) HK HG HMF HA).
    intros r Hr. unfold acallee_saved in Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                 r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    + transitivity (Z_to_bv 64 (spZ regs - 160 + 160)); [clw_reg HX|].
      replace (spZ regs - 160 + 160) with (spZ regs) by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
    + clw_reg HX.
Qed.

(* ---- the loop ---- *)

(* The configuration at tagged_of's return (0x8499c) in a round at pos: a0 = t = g_cmd + 40 s, the callee-saved
   registers of the loop head, the invariant at the world Bc, the frame. *)
Definition clw_at_tret (pos dispc s : Z) (Bc j0 : list byte) (c : config) : Prop :=
  exists (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
    c = mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 543132) mem2 (YK11.seg_rom tfibsegs)) md2 /\
    clw_inv mem2 md2 Bc dispc /\ clw_fr mem2 j0 /\
    YK11.getr regs2 (Z_to_bv 5 2) = Z_to_bv 64 spv /\ YK11.getr regs2 (Z_to_bv 5 3) = gp0 /\
    YK11.getr regs2 (Z_to_bv 5 4) = tp0 /\ YK11.getr regs2 (Z_to_bv 5 8) = Z_to_bv 64 dp /\
    YK11.getr regs2 (Z_to_bv 5 9) = Z_to_bv 64 len /\
    YK11.getr regs2 (Z_to_bv 5 10) = Z_to_bv 64 (6180992 + 40 * s) /\
    YK11.getr regs2 (Z_to_bv 5 18) = Z_to_bv 64 bp /\
    YK11.getr regs2 (Z_to_bv 5 21) = Z_to_bv 64 (bp + pos) /\
    YK11.getr regs2 (Z_to_bv 5 22) = Z_to_bv 64 (len - pos) /\
    YK11.getr regs2 (Z_to_bv 5 23) = Z_to_bv 64 2147450880 /\
    YK11.getr regs2 (Z_to_bv 5 25) = Z_to_bv 64 pos /\
    YK11.getr regs2 (Z_to_bv 5 26) = Z_to_bv 64 1023 /\
    YK11.getr regs2 (Z_to_bv 5 27) = Z_to_bv 64 6158660.

(* The configuration at bcmp's return (0x849f4) in a round at pos: a0 = 0, s3 = t, s4 = t->len, s8 = t's shadow
   address, the other callee-saved registers of the loop head, the invariant at the world Bc, the frame. *)
Definition clw_at_bret (pos dispc s : Z) (Bc j0 : list byte) (c : config) : Prop :=
  exists (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model),
    c = mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 543220) mem3 (YK11.seg_rom tfibsegs)) md3 /\
    clw_inv mem3 md3 Bc dispc /\ clw_fr mem3 j0 /\
    YK11.getr regs3 (Z_to_bv 5 2) = Z_to_bv 64 spv /\ YK11.getr regs3 (Z_to_bv 5 3) = gp0 /\
    YK11.getr regs3 (Z_to_bv 5 4) = tp0 /\ YK11.getr regs3 (Z_to_bv 5 8) = Z_to_bv 64 dp /\
    YK11.getr regs3 (Z_to_bv 5 9) = Z_to_bv 64 len /\
    YK11.getr regs3 (Z_to_bv 5 10) = Z_to_bv 64 0 /\
    YK11.getr regs3 (Z_to_bv 5 18) = Z_to_bv 64 bp /\
    YK11.getr regs3 (Z_to_bv 5 19) = Z_to_bv 64 (6180992 + 40 * s) /\
    YK11.getr regs3 (Z_to_bv 5 20) = Z_to_bv 64 (TW.Cmd_len Bc s) /\
    YK11.getr regs3 (Z_to_bv 5 21) = Z_to_bv 64 (bp + pos) /\
    YK11.getr regs3 (Z_to_bv 5 22) = Z_to_bv 64 (len - pos) /\
    YK11.getr regs3 (Z_to_bv 5 23) = Z_to_bv 64 2147450880 /\
    YK11.getr regs3 (Z_to_bv 5 24) = Z_to_bv 64 ((6180992 + 40 * s) / 8 + 2147450880) /\
    YK11.getr regs3 (Z_to_bv 5 25) = Z_to_bv 64 pos /\
    YK11.getr regs3 (Z_to_bv 5 26) = Z_to_bv 64 1023 /\
    YK11.getr regs3 (Z_to_bv 5 27) = Z_to_bv 64 6158660.

(* The loop's statement at one fuel. *)
Definition clw_loop_P (fuel : nat) : Prop :=
  forall pos dispc (Bc : list byte) (m : word -> option byte) (md : Model) (ms : machine_state)
    (j0 : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31 : word),
  TC.latest_sent_loop fuel Bc body len pos dispc = Some (Bw', disp) ->
  0 <= pos < len ->
  clw_inv m md Bc dispc ->
  length j0 = 8%nat -> clw_fr m j0 ->
  Regs6ss.ms_eqv (MS (cls_regs_head x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31
                        gp0 tp0 spv dp bp len pos)
                    (@YK11.fp_regs fx) (Z_to_bv 64 543092) (@YK11.fp_csr fx) None m (YK11.seg_rom rsegs)) ms ->
  SRr tfibsegs W (mkCfg ms md) clw_post.

(* helpers of the loop (lead) *)

Lemma clw_addr_sub : forall (m : word -> option byte) p n o n',
  FCW.addressable m p n -> 0 <= o -> 0 <= n' -> o + n' <= n -> FCW.addressable m (p + o) n'.
Proof.
  intros m p n o n' (H0 & H1 & H2 & HA) Ho Hn' Hon.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p + o + i) with (p + (o + i)) by lia. apply HA. lia.
Qed.

(* the four bytes at dp are present at every memory the walk reaches *)
Lemma clw_pres_dp : forall m, clw_grow m -> forall a, dp <= a < dp + 4 -> apresent (w_H W) m a.
Proof.
  intros m HG a Ha. destruct (HTWR a Ha) as [(_ & Hp & _) | HGa].
  - exact (HG a Hp).
  - exfalso. exact (HDG a Ha HGa).
Qed.

(* end of the helpers of the loop *)

(* The first cut of a round: the pre run (the loop head to the `jal` at 0x84998), then the call of tagged_of. *)
Lemma clw_seg_tag : forall pos dispc s (Bc : list byte) (m : word -> option byte) (md : Model) (ms : machine_state)
    (j0 : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31 : word),
  0 <= pos < len -> 3 <= len - pos ->
  TW.u_at body pos 1 = TC.TAG ->
  s = Z.lor (Z.shiftl (TW.u_at body (pos + 2) 1) 7) (TW.u_at body (pos + 1) 1) ->
  0 <= s < TC.CMDS_MAX -> s < TW.g_ncmd Bc ->
  clw_inv m md Bc dispc ->
  length j0 = 8%nat -> clw_fr m j0 ->
  Regs6ss.ms_eqv (MS (cls_regs_head x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31
                        gp0 tp0 spv dp bp len pos)
                    (@YK11.fp_regs fx) (Z_to_bv 64 543092) (@YK11.fp_csr fx) None m (YK11.seg_rom rsegs)) ms ->
  (forall c, clw_at_tret pos dispc s Bc j0 c -> SRr tfibsegs W c clw_post) ->
  SRr tfibsegs W (mkCfg ms md) clw_post.
Proof.
  intros pos dispc s Bc m md ms j0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31
    Hpos H3 HTAG Hsdef Hs Hsnc HI Hj0 HFR HE K.
  pose proof clw_stack as (Hce & H47 & Hsp0 & HSTK0 & ECS & Hpres).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  pose proof clw_bounds as HBDS. pose proof clw_rng as HRNG.
  pose proof HBDS as (Bsp0 & Bsp1 & Bdp0 & Bdp1 & Bbp0 & Blen0 & Bbp1 & Bdp4).
  destruct HI as (HJm & HKm & HGm & HMm & HLBc & HICc & HAGc).
  pose proof HMm as (HWm & HDPm & HBYm & HACm & HAQm & HADm & HABm & HWOKm).
  assert (EST : ESTACK = 4096) by reflexivity.
  (* ---- the pre run: the loop head to the tagged_of entry ---- *)
  apply (cls_chain W _ 543092 m md ms
           (fun ms1 => ms1 = MS (cls_regs_tag x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x20 x24 x28 x29 x30 x31 gp0 tp0
                                  spv dp bp len pos)
                              (@YK11.fp_regs fx) (Z_to_bv 64 542368) (@YK11.fp_csr fx) None m (YK11.seg_rom rsegs))
           _ HE).
  { refine (cls_run_pre RNGW _ m (@YK11.fp_regs fx) (@YK11.fp_csr fx) spv dp bp len pos j0
              ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110
              x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31 gp0 tp0
              HBDS HRNG Hpos HFR Hj0 _).
    eexists. split; [apply ExecF.mstepsF_refl | reflexivity]. }
  intros ms1 ms3 md1 -> HE3 _ Hsb1.
  pose proof (clw_sbm_step m md md1 HJm Hsb1) as HJm1.
  destruct (@decode_eqv_mkst fx _ _ _ _ HE3) as (R3 & -> & HX3).
  (* the registers at the call *)
  assert (G1 : YK11.getr R3 (Z_to_bv 5 1) = Z_to_bv 64 543132) by clw_reg HX3.
  assert (G2 : YK11.getr R3 (Z_to_bv 5 2) = Z_to_bv 64 spv) by clw_reg HX3.
  assert (G3 : YK11.getr R3 (Z_to_bv 5 3) = gp0) by clw_reg HX3.
  assert (G4 : YK11.getr R3 (Z_to_bv 5 4) = tp0) by clw_reg HX3.
  assert (G8 : YK11.getr R3 (Z_to_bv 5 8) = Z_to_bv 64 dp) by clw_reg HX3.
  assert (G9 : YK11.getr R3 (Z_to_bv 5 9) = Z_to_bv 64 len) by clw_reg HX3.
  assert (G10 : YK11.getr R3 (Z_to_bv 5 10) = Z_to_bv 64 (bp + pos)) by clw_reg HX3.
  assert (G11 : YK11.getr R3 (Z_to_bv 5 11) = Z_to_bv 64 (len - pos)) by clw_reg HX3.
  assert (G18 : YK11.getr R3 (Z_to_bv 5 18) = Z_to_bv 64 bp) by clw_reg HX3.
  assert (G21 : YK11.getr R3 (Z_to_bv 5 21) = Z_to_bv 64 (bp + pos)) by clw_reg HX3.
  assert (G22 : YK11.getr R3 (Z_to_bv 5 22) = Z_to_bv 64 (len - pos)) by clw_reg HX3.
  assert (G23 : YK11.getr R3 (Z_to_bv 5 23) = Z_to_bv 64 2147450880) by clw_reg HX3.
  assert (G25 : YK11.getr R3 (Z_to_bv 5 25) = Z_to_bv 64 pos) by clw_reg HX3.
  assert (G26 : YK11.getr R3 (Z_to_bv 5 26) = Z_to_bv 64 1023) by clw_reg HX3.
  assert (G27 : YK11.getr R3 (Z_to_bv 5 27) = Z_to_bv 64 6158660) by clw_reg HX3.
  assert (GSP : spZ R3 = spv).
  { change (bv_unsigned (YK11.getr R3 (Z_to_bv 5 2)) = spv). rewrite G2. apply unsigned_lit.
    pose proof HBDS as (B1 & B2' & _). lia. }
  (* ---- the call of tagged_of ---- *)
  rewrite <- clw_tag_at.
  eapply SRr_bind.
  { apply (@cls_tagged fx rc B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md1 k R3 (spv - sp0) (bp + pos)
             (len - pos) (skipn (Z.to_nat pos) body) Bc (Some s) HCELLS LEAF HJm1).
    - rewrite GSP. lia.
    - pose proof (Z.mod_pos_bound (spv - sp0) 16 ltac:(lia)).
      assert (E : spv - sp0 = (spZ regs - sp0) - 160) by lia. rewrite E.
      rewrite Zminus_mod, (Zminus_mod (spZ regs) sp0), Hsp16, Hsp0. reflexivity.
    - lia.
    - rewrite EST. lia.
    - exact (eq_trans G3 Hgp).
    - exact (eq_trans G4 Htp).
    - change (YK0s.ret_ok (YK11.getr R3 (Z_to_bv 5 1))). rewrite G1.
      apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - exact G10.
    - exact G11.
    - lia.
    - lia.
    - replace (bp + pos) with (bp + Z.of_nat (Z.to_nat pos)) by lia.
      apply cls_bytes_skipn; [exact HBYm | lia].
    - exact HWm.
    - apply (cls_tag_m Bc body len pos s Hlen (proj1 Hpos) H3 HTAG Hsdef Hs Hsnc).
    - intros _. rewrite GSP. unfold decode_off_win in HOW. lia.
    - intros _. apply (clw_addr_sub m bp len pos 3 HABm); lia.
    - intros _ i Hi. replace (bp + pos + i) with (bp + (pos + i)) by lia. apply clw_body_vis. lia.
    - intros _ x Hx.
      assert (Ex : x = FCW.shadow_addr (bp + pos) \/ x = FCW.shadow_addr (bp + (pos + 2))).
      { replace (bp + pos + 2) with (bp + (pos + 2)) in Hx by lia. unfold FCW.shadow_addr in *.
        Z.div_mod_to_equations. lia. }
      destruct Ex as [-> | ->]; apply clw_body_shvis; lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HR2 & HK2 & HG2).
  rewrite GSP in HK2.
  (* the invariant at the return *)
  destruct (clw_call_step m mem2 (spv - ESTACK) ltac:(rewrite EST; lia) HK2 HG2 HKm HGm) as (HK3 & HG3).
  assert (HM2 : cls_mem mem2 Bc body dp bp len (Z_to_bv 64 dispc)).
  { apply (cls_mem_call W m mem2 Bc body dp bp len (Z_to_bv 64 dispc) (spv - ESTACK) spv HMm Hlen HK2 HG2).
    - intros a Ha. destruct (clw_membytes a Ha) as (Ha1 & Ha2 & Ha3).
      split; [exact Ha1|]. split; [rewrite EST; lia | exact Ha3].
    - exact (clw_pres_dp m HGm). }
  assert (HFR2 : clw_fr mem2 j0).
  { unfold clw_fr. apply (clw_fr_call m mem2 md1 md2 (spv - ESTACK)
      (cls_fr j0 dp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ltac:(rewrite EST; lia) HJm1 HJ2 HK2).
    - cbn [cls_fr Cells.cells_size Cells.csize]. first [reflexivity | rewrite Hj0; reflexivity | lia].
    - exact HFR. }
  apply K.
  exists regs2, mem2, md2. split; [rewrite <- G1; reflexivity|].
  split; [split; [exact HJ2|]; split; [exact HK3|]; split; [exact HG3|]; split; [exact HM2|];
          split; [exact HLBc|]; split; [exact HICc | exact HAGc]|].
  split; [exact HFR2|].
  assert (CS : forall r, 18 <= r <= 27 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 ->
    YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr R3 (Z_to_bv 5 r)).
  { intros r Hr. apply HP2. hnf. lia. }
  split; [rewrite (CS 2 ltac:(lia)); exact G2|].
  split; [rewrite (CS 3 ltac:(lia)); exact G3|].
  split; [rewrite (CS 4 ltac:(lia)); exact G4|].
  split; [rewrite (CS 8 ltac:(lia)); exact G8|].
  split; [rewrite (CS 9 ltac:(lia)); exact G9|].
  split; [exact HR2|].
  split; [rewrite (CS 18 ltac:(lia)); exact G18|].
  split; [rewrite (CS 21 ltac:(lia)); exact G21|].
  split; [rewrite (CS 22 ltac:(lia)); exact G22|].
  split; [rewrite (CS 23 ltac:(lia)); exact G23|].
  split; [rewrite (CS 25 ltac:(lia)); exact G25|].
  split; [rewrite (CS 26 ltac:(lia)); exact G26|].
  rewrite (CS 27 ltac:(lia)); exact G27.
Qed.

(* helpers of the second cut (SegBcmp) *)

(* a callee-saved register after the bcmp call: the call keeps it (HP, aregs_preserved), and the call state's map is
   register-equivalent (HX) to cls_regs_call *)
Local Ltac clw_breg HP HX :=
  lazymatch goal with |- YK11.getr _ (Z_to_bv 5 ?r) = _ => rewrite (HP r ltac:(hnf; lia)); clw_reg HX end.

(* a byte of the body, read at a memory where cls_mem holds *)
Lemma clw_body_view : forall (m : word -> option byte) (Bc : list byte) (v : word) (i : Z),
  cls_mem m Bc body dp bp len v -> 0 <= i < len ->
  aview tfibsegs (w_H W) m (bp + i) = option_map (fun b : byte => bv_unsigned b) (nth_error body (Z.to_nat i)).
Proof.
  intros m Bc v i HMm Hi.
  destruct HMm as (_ & _ & Hb & _). unfold cls_body in Hb. destruct Hb as (_ & _ & Hb).
  rewrite (cls_aview_csw W m (bp + i) (clw_body_vis i Hi)). unfold csw_view.
  rewrite <- (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* a byte of g_cmd's payload, read at a memory where cls_mem holds *)
Lemma clw_cmd_view : forall (m : word -> option byte) (Bc : list byte) (v : word) (j : Z),
  cls_mem m Bc body dp bp len v -> 0 <= j < 40960 ->
  aview tfibsegs (w_H W) m (6180992 + j) =
    Some (bv_unsigned (nth (Z.to_nat (TW.OFF_g_cmd + j)) Bc (Z_to_bv 8 0))).
Proof.
  intros m Bc v j HMm Hj.
  assert (Hin : tw_in TMAP_B (6180992 + j)).
  { exists TW.OFF_g_cmd, TB_g_cmd, TW.SZ_g_cmd. split; [exact TMAP_B_g_cmd | unfold TB_g_cmd, TW.SZ_g_cmd; lia]. }
  rewrite (cls_aview_csw W m (6180992 + j) (cls_vis W _ Hin)).
  destruct HMm as ((_ & Htw) & _).
  exact (Htw TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd j TMAP_B_g_cmd ltac:(unfold TW.SZ_g_cmd; lia)).
Qed.

(* the read facts of a sub-range of the body at a memory where cls_mem holds and every byte of the shadow band
   [kLowMemEnd, kHighShadowEnd) keeps its view (clw_kept: the band is below the call's window, apart from dp and
   from every byte the walk stores) *)
Lemma clw_bcmp_body_rd : forall (m : word -> option byte) (Bc : list byte) (v : word) (q n : Z),
  cls_mem m Bc body dp bp len v -> clw_kept m -> bp <= q -> 0 <= n -> q + n <= bp + len -> 0 < len ->
  decode_rd_ok W m q n.
Proof.
  intros m Bc v q n HMm HKm H1 Hn H2 Hl.
  destruct clw_mem0 as (v0 & HM0).
  pose proof clw_stack as (Hce & _ & _ & _ & ECS & _).
  pose proof (@YM05.alloc_ceiling_value rc) as [[CE1 _] _].
  pose proof clw_app_dp as HAD. unfold cls_app, FCW.LOWMEM_END, FCW.HIGHMEM_BEG, FCW.APPMEM_END in HAD.
  apply (trans_rd_ok_view W W memc m q n).
  - exact (trans_rd_ok_sub W memc bp len q n (clw_body_rd Hl) H1 H2 Hn).
  - intros a Ha. replace a with (bp + (a - bp)) by lia.
    rewrite (clw_body_view m Bc v (a - bp) HMm ltac:(lia)), (clw_body_view memc Bw v0 (a - bp) HM0 ltac:(lia)).
    reflexivity.
  - intros sa Hsa. unfold kLowMemEnd, kHighShadowEnd in Hsa.
    apply HKm; [lia | lia | | lia].
    intros Hw.
    assert (Hnd : ~ (dp <= sa < dp + 4)) by lia.
    pose proof (cls_wr_low B HGX dp sa Hw Hnd) as X. unfold kLowMemEnd in X. lia.
Qed.

(* g_cmd's payload is addressable with its hull's shadow visible at every journal state: its shadow is 0
   (trans_cls_cells) *)
Lemma clw_cmd_ra : forall (m : word -> option byte) (md : Model) (q n : Z),
  clw_J m md -> 6180992 <= q -> q + n <= 6180992 + 40960 ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF q n /\
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) m) q n).
Proof.
  intros m md q n HJm H1 H2.
  pose proof (ajournal_gx_AR tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJm) as HAR.
  destruct (Z_lt_le_dec 0 n) as [Hn|Hn].
  - pose proof (Z.div_mod q 64 ltac:(lia)). pose proof (Z.mod_pos_bound q 64 ltac:(lia)).
    pose proof (Z.div_mod (q + n - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 64 ltac:(lia)).
    destruct (decode_zshadow_ra B lyc Sc W m md TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd) q n HAR (proj2 HSC) Hn
                ltac:(unfold TB_g_cmd; lia) ltac:(unfold TB_g_cmd, TW.SZ_g_cmd; lia)) as [A1 A2].
    split; [exact A1 | intros _; exact A2].
  - split; [intros x Hx; lia | intros Hn'; lia].
Qed.

(* bcmp's two ranges hold the same bytes: the body's bytes at pos and t->bytes are the round's sub equality *)
Lemma clw_bcmp_agree : forall (m : word -> option byte) (Bc : list byte) (v : word) (pos s n : Z),
  cls_mem m Bc body dp bp len v -> Z.of_nat (length Bc) = TW.W_LEN ->
  0 <= pos -> 0 <= s < 1024 -> 0 <= n <= 24 -> pos + n <= len ->
  TW.sub body pos (Z.to_nat n) = TW.sub Bc (TW.A_Cmd_bytes s) (Z.to_nat n) ->
  forall i, 0 <= i < n ->
  aview tfibsegs (w_H W) m (bp + pos + i) = aview tfibsegs (w_H W) m (6180992 + 40 * s + 12 + i).
Proof.
  intros m Bc v pos s n HMm HLB Hp Hs Hn Hpn HSUB i Hi.
  assert (E : nth_error body (Z.to_nat pos + Z.to_nat i)%nat =
              nth_error Bc (Z.to_nat (TW.A_Cmd_bytes s) + Z.to_nat i)%nat).
  { pose proof (f_equal (fun l => nth_error l (Z.to_nat i)) HSUB) as X. cbv beta in X. unfold TW.sub in X.
    rewrite !nth_error_firstn in X.
    assert (L : (Z.to_nat i <? Z.to_nat n)%nat = true) by (apply Nat.ltb_lt; lia).
    rewrite L, !nth_error_skipn in X. exact X. }
  replace (bp + pos + i) with (bp + (pos + i)) by lia.
  replace (6180992 + 40 * s + 12 + i) with (6180992 + (40 * s + 12 + i)) by lia.
  rewrite (clw_body_view m Bc v (pos + i) HMm ltac:(lia)).
  rewrite (clw_cmd_view m Bc v (40 * s + 12 + i) HMm ltac:(lia)).
  rewrite (Z2Nat.inj_add pos i) by lia. rewrite E.
  assert (EI : (Z.to_nat (TW.A_Cmd_bytes s) + Z.to_nat i)%nat = Z.to_nat (TW.OFF_g_cmd + (40 * s + 12 + i)))
    by (unfold TW.A_Cmd_bytes, TW.OFF_g_cmd; lia).
  rewrite EI.
  rewrite (nth_error_nth' Bc (Z_to_bv 8 0)) by (unfold TW.W_LEN in HLB; unfold TW.OFF_g_cmd; lia).
  reflexivity.
Qed.

(* end of the helpers of the second cut *)

(* The second cut: the mid run (tagged_of's return to the `jal` at 0x849f0), then the call of the bcmp wrapper,
   whose result is 0 because the model's bytes agree. *)
Lemma clw_seg_bcmp : forall pos dispc s (Bc j0 : list byte) (c : config),
  0 <= pos < len -> 3 <= len - pos -> 0 <= s < TC.CMDS_MAX -> s < TW.g_ncmd Bc ->
  TW.Cmd_st Bc s = TC.PENDING -> TW.Cmd_len Bc s <= len - pos ->
  TW.sub body pos (Z.to_nat (TW.Cmd_len Bc s)) = TW.sub Bc (TW.A_Cmd_bytes s) (Z.to_nat (TW.Cmd_len Bc s)) ->
  length j0 = 8%nat ->
  clw_at_tret pos dispc s Bc j0 c ->
  (forall c', clw_at_bret pos dispc s Bc j0 c' -> SRr tfibsegs W c' clw_post) ->
  SRr tfibsegs W c clw_post.
Proof.
  intros pos dispc s Bc j0 c Hpos H3 Hs Hsnc HST HTL HSUB Hj0 Hc K.
  destruct Hc as (regs2 & mem2 & md2 & -> & HI & HFR & T2 & T3 & T4 & T8 & T9 & T10 & T18 & T21 & T22 & T23 &
                  T25 & T26 & T27).
  pose proof HI as (HJ2 & HK2 & HG2 & HMm & HLB & HIC & HAG).
  pose proof clw_stack as (Hce & H47 & Hsp0 & HSTK0 & ECS & Hpres).
  pose proof clw_bounds as HBDS. unfold cls_bounds in HBDS.
  pose proof (@YM05.alloc_ceiling_value rc) as [[CE1 CE2] _].
  pose proof (cls_cmd_len_range Bc s) as Rtl.
  assert (Htl : TW.Cmd_len Bc s <= 24).
  { pose proof (HIC s ltac:(lia) ltac:(lia) HST) as X. unfold DSpec.SPEC_CMD_MAX in X. exact X. }
  pose proof Hs as Hs'. unfold TC.CMDS_MAX in Hs'.
  change (SRr tfibsegs W (@cfg_at fx tfibsegs 543132 regs2 mem2 md2) clw_post).
  apply (@decode_run fx W regs2 mem2 md2 543132
    (fun ms => ms = MS (cls_regs_call (YK11.getr regs2 (Z_to_bv 5 5)) (YK11.getr regs2 (Z_to_bv 5 6))
                          (YK11.getr regs2 (Z_to_bv 5 7)) (YK11.getr regs2 (Z_to_bv 5 13))
                          (YK11.getr regs2 (Z_to_bv 5 14)) (YK11.getr regs2 (Z_to_bv 5 15))
                          (YK11.getr regs2 (Z_to_bv 5 16)) (YK11.getr regs2 (Z_to_bv 5 17))
                          (YK11.getr regs2 (Z_to_bv 5 28)) (YK11.getr regs2 (Z_to_bv 5 29))
                          (YK11.getr regs2 (Z_to_bv 5 30)) (YK11.getr regs2 (Z_to_bv 5 31))
                          gp0 tp0 spv dp bp len pos s (TW.Cmd_len Bc s))
                    (@YK11.fp_regs fx) (Z_to_bv 64 273716) (@YK11.fp_csr fx) None mem2 (YK11.seg_rom rsegs))).
  - (* the mid run: tagged_of's return to the `jal` of the bcmp wrapper; it stores nothing *)
    unfold LCW.ms_of_regs.
    rewrite T2, T3, T4, T8, T9, T10, T18, T21, T22, T23, T25, T26, T27.
    refine (cls_run_mid RNGW _ mem2 (@YK11.fp_regs fx) (@YK11.fp_csr fx) spv dp bp len pos s Bc body
              (Z_to_bv 64 dispc) j0 ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110
              (YK11.getr regs2 (Z_to_bv 5 1)) (YK11.getr regs2 (Z_to_bv 5 5)) (YK11.getr regs2 (Z_to_bv 5 6))
              (YK11.getr regs2 (Z_to_bv 5 7)) (YK11.getr regs2 (Z_to_bv 5 11)) (YK11.getr regs2 (Z_to_bv 5 12))
              (YK11.getr regs2 (Z_to_bv 5 13)) (YK11.getr regs2 (Z_to_bv 5 14)) (YK11.getr regs2 (Z_to_bv 5 15))
              (YK11.getr regs2 (Z_to_bv 5 16)) (YK11.getr regs2 (Z_to_bv 5 17)) (YK11.getr regs2 (Z_to_bv 5 19))
              (YK11.getr regs2 (Z_to_bv 5 20)) (YK11.getr regs2 (Z_to_bv 5 24)) (YK11.getr regs2 (Z_to_bv 5 28))
              (YK11.getr regs2 (Z_to_bv 5 29)) (YK11.getr regs2 (Z_to_bv 5 30)) (YK11.getr regs2 (Z_to_bv 5 31))
              gp0 tp0 clw_bounds clw_rng HLB Hpos Hs HST HTL HFR Hj0 HMm _).
    apply ExecF.evtF_done. reflexivity.
  - (* the call of the bcmp wrapper *)
    intros ms1 ms2 md3 HP HE _ Hsb. cbv beta in HP. subst ms1.
    destruct (@decode_eqv_mkst fx _ _ _ _ HE) as (R4 & -> & HX).
    pose proof (clw_sbm_step mem2 md2 md3 HJ2 Hsb) as HJ3.
    assert (G2 : YK11.getr R4 (Z_to_bv 5 2) = Z_to_bv 64 spv) by clw_reg HX.
    assert (ESP4 : spZ R4 = spv).
    { change (spZ R4) with (bv_unsigned (YK11.getr R4 (Z_to_bv 5 2))). rewrite G2.
      exact (wa_unsigned spv ltac:(lia)). }
    assert (P10 : YK11.getr R4 10 = w64 (bp + pos)) by clw_reg HX.
    assert (P11 : YK11.getr R4 11 = w64 (6180992 + 40 * s + 12)) by clw_reg HX.
    assert (P12 : YK11.getr R4 12 = w64 (TW.Cmd_len Bc s)) by clw_reg HX.
    assert (Pn : 0 <= TW.Cmd_len Bc s < 2 ^ 32) by lia.
    pose proof (clw_bcmp_body_rd mem2 Bc (Z_to_bv 64 dispc) (bp + pos) (TW.Cmd_len Bc s) HMm HK2
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (BRv & BRa & BRh & BRm & BR0 & BR63).
    assert (Px0 : 0 <= bp + pos) by lia.
    assert (Py0 : 0 <= 6180992 + 40 * s + 12) by lia.
    assert (Pyn : 6180992 + 40 * s + 12 + TW.Cmd_len Bc s <= 2 ^ 63) by lia.
    assert (Psp : spZ R4 = sp0 + (spv - sp0)) by lia.
    assert (Pal : (spv - sp0) mod 16 = 0).
    { pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
      rewrite Hsp16 in D1. rewrite Hsp0 in D2.
      replace (spZ regs - 160 - sp0) with ((spZ regs / 16 - sp0 / 16 - 10) * 16) by lia.
      apply Z.mod_mul. lia. }
    assert (Pneg : spv - sp0 <= 0) by lia.
    assert (Pbud : 2 * ESTACK - (spv - sp0) <= STK) by (unfold ESTACK; lia).
    assert (Pgp : YK11.getr R4 3 = w64 (as_gp B))
      by (transitivity (YK11.getr regs (Z_to_bv 5 3)); [clw_reg HX | exact Hgp]).
    assert (Ptp : YK11.getr R4 4 = w64 (as_tp B))
      by (transitivity (YK11.getr regs (Z_to_bv 5 4)); [clw_reg HX | exact Htp]).
    assert (Pra : YK11.getr R4 1 = Z_to_bv 64 543220) by clw_reg HX.
    assert (Prok : YK0s.ret_ok (Z_to_bv 64 543220)) by (apply YK0s.ret_ok_even; vm_compute; reflexivity).
    assert (Psx : src_ok tfibsegs W R4 mem2 (bp + pos) (TW.Cmd_len Bc s)).
    { intros a Ha. split; [exact (BRv a Ha)|]. rewrite ESP4. unfold decode_off_win in HOW. unfold ESTACK. lia. }
    assert (Psy : src_ok tfibsegs W R4 mem2 (6180992 + 40 * s + 12) (TW.Cmd_len Bc s)).
    { intros a Ha. split.
      - replace a with (6180992 + (a - 6180992)) by lia.
        rewrite (clw_cmd_view mem2 Bc (Z_to_bv 64 dispc) (a - 6180992) HMm ltac:(lia)). discriminate.
      - rewrite ESP4. unfold ESTACK. lia. }
    assert (Pwx : forall a, bp + pos <= a < bp + pos + TW.Cmd_len Bc s ->
              ~ (sp0 + (spv - sp0) - 2 * ESTACK <= a < sp0 + (spv - sp0))).
    { intros a Ha. unfold decode_off_win in HOW. unfold ESTACK. lia. }
    assert (Pwy : forall a, 6180992 + 40 * s + 12 <= a < 6180992 + 40 * s + 12 + TW.Cmd_len Bc s ->
              ~ (sp0 + (spv - sp0) - 2 * ESTACK <= a < sp0 + (spv - sp0))).
    { intros a Ha. unfold ESTACK. lia. }
    assert (Pmy : amem_range (6180992 + 40 * s + 12) (TW.Cmd_len Bc s)) by (unfold amem_range, kLowMemEnd; lia).
    destruct (clw_cmd_ra mem2 md3 (6180992 + 40 * s + 12) (TW.Cmd_len Bc s) HJ3 ltac:(lia) ltac:(lia))
      as [Pry Phy].
    rewrite <- clw_bcmp_at.
    eapply SRr_bind.
    { exact (@cls_bcmp fx rc B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md3 k R4
               (bp + pos) (6180992 + 40 * s + 12) (TW.Cmd_len Bc s) (spv - sp0) (Z_to_bv 64 543220)
               (HBC fx) HJ3 P10 P11 P12 Pn Px0 BR63 Py0 Pyn Psp Pal Pneg Pbud Pgp Ptp Pra Prok Psx Psy Pwx Pwy
               BRm Pmy BRa (fun _ => BRh) Pry Phy). }
    intros W2 c2 _ HQ. cbv beta in HQ.
    destruct HQ as (-> & regs3 & mem3 & md4 & -> & HJ4 & v & HP3 & HR3 & HCMP & HK3 & HG3).
    (* bcmp's answer is 0: the two ranges hold the same bytes *)
    assert (V0 : v = w64 0).
    { apply HCMP. intros i Hi.
      exact (clw_bcmp_agree mem2 Bc (Z_to_bv 64 dispc) pos s (TW.Cmd_len Bc s) HMm HLB ltac:(lia) ltac:(lia)
               ltac:(lia) ltac:(lia) HSUB i Hi). }
    (* what the call keeps: every byte outside its window [spv - 2 ESTACK, spv) *)
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spv - 8192 <= a < spv) ->
              aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mem2 a).
    { intros a Ha Hn. apply HK3; [exact Ha | unfold ESTACK; lia]. }
    destruct (clw_call_step mem2 mem3 (spv - 8192) ltac:(lia) K3 HG3 HK2 HG2) as [HK4 HG4].
    assert (HM4 : cls_mem mem3 Bc body dp bp len (Z_to_bv 64 dispc)).
    { apply (cls_mem_call W mem2 mem3 Bc body dp bp len (Z_to_bv 64 dispc) (spv - 8192) spv HMm Hlen K3 HG3).
      - intros a Ha. destruct (clw_membytes a Ha) as (A1 & A2 & A3).
        split; [exact A1|]. split; [lia | exact A3].
      - intros a Ha. apply HG2.
        destruct (HTWR a Ha) as [(_ & Hp & _) | Hg]; [exact Hp | exfalso; exact (HDG a Ha Hg)]. }
    assert (HFR3 : clw_fr mem3 j0).
    { unfold clw_fr in HFR |- *.
      apply (clw_fr_call mem2 mem3 md3 md4 (spv - 8192) _ ltac:(lia) HJ3 HJ4 K3); [reflexivity | exact HFR]. }
    apply K. unfold clw_at_bret. exists regs3, mem3, md4.
    split; [reflexivity|].
    split.
    { split; [exact HJ4|]. split; [exact HK4|]. split; [exact HG4|]. split; [exact HM4|].
      split; [exact HLB|]. split; [exact HIC | exact HAG]. }
    split; [exact HFR3|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    split; [transitivity v; [exact HR3 | rewrite V0; reflexivity]|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    split; [clw_breg HP3 HX|].
    clw_breg HP3 HX.
Qed.

(* helpers of the rest of a round (SegPost) *)

(* end of the helpers of the rest of a round *)

(* The rest of a round: the post run (bcmp's return to the next loop head or the epilogue). *)
Lemma clw_seg_post : forall fuel pos dispc s (Bc B2 j0 : list byte) (c : config),
  clw_loop_P fuel ->
  0 <= pos -> 3 <= len - pos -> 0 <= s < TC.CMDS_MAX -> s < TW.g_ncmd Bc ->
  TW.Cmd_len Bc s <= len - pos ->
  TC.q_remove_m (TW.set_Cmd_st Bc s TC.SENT) s = Some (B2, tt) ->
  TC.latest_sent_loop fuel B2 body len (pos + TW.Cmd_len Bc s) (Z.lor dispc (TW.Cmd_display B2 s)) =
    Some (Bw', disp) ->
  length j0 = 8%nat ->
  clw_at_bret pos dispc s Bc j0 c ->
  SRr tfibsegs W c clw_post.
Proof.
  intros fuel pos dispc s Bc B2 j0 c IH Hpos H3 Hs Hsnc HTL HQR HL2 Hj0 Hc.
  destruct Hc as (regs3 & mem3 & md3 & -> & HI & HFR & T2 & T3 & T4 & T8 & T9 & T10 & T18 & T19 & T20 & T21 & T22 &
                  T23 & T24 & T25 & T26 & T27).
  destruct HI as (HJ3 & HK3 & HG3 & HMm & HLB & HIC & HAG).
  pose proof (cls_cmd_len_range Bc s) as RTL.
  (* the bytes of g_cmd's payload that are not an st field keep their value across the round *)
  assert (HAG2 : clw_agree B2).
  { intros j i Hj Hi. rewrite (cls_agree_round Bc s B2 HLB Hs HQR j i Hj Hi). exact (HAG j i Hj Hi). }
  change (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 543220) mem3 (YK11.seg_rom tfibsegs)) md3)
    with (@cfg_at fx tfibsegs 543220 regs3 mem3 md3).
  apply (@decode_run fx W regs3 mem3 md3 543220
    (fun ms1 =>
       (exists (m' : word -> option byte) (j : list byte)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
           y28 y29 y30 y31 : word),
          ms1 = MS (Frame.mkR y1 (Z_to_bv 64 spv) gp0 tp0 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                       y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                   (@YK11.fp_regs fx) (Z_to_bv 64 543564) (@YK11.fp_csr fx) None m' (YK11.seg_rom rsegs) /\
          length j = 56%nat /\ clw_fre m' j /\
          cls_mem m' B2 body dp bp len (Z_to_bv 64 (Z.lor dispc (TW.Cmd_display B2 s))) /\
          Frame.munch (cls_W spv dp) mem3 m' /\ YK1b.mem_grows mem3 m' /\ len <= pos + TW.Cmd_len Bc s) \/
       (exists (m' : word -> option byte) (j0' : list byte)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y24 y28 y29 y30 y31 : word),
          ms1 = MS (cls_regs_head y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y24 y28 y29 y30 y31
                      gp0 tp0 spv dp bp len (pos + TW.Cmd_len Bc s))
                   (@YK11.fp_regs fx) (Z_to_bv 64 543092) (@YK11.fp_csr fx) None m' (YK11.seg_rom rsegs) /\
          length j0' = 8%nat /\ clw_fr m' j0' /\
          cls_mem m' B2 body dp bp len (Z_to_bv 64 (Z.lor dispc (TW.Cmd_display B2 s))) /\
          Frame.munch (cls_W spv dp) mem3 m' /\ YK1b.mem_grows mem3 m' /\ pos + TW.Cmd_len Bc s < len))).
  - unfold LCW.ms_of_regs.
    rewrite T2, T3, T4, T8, T9, T10, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27.
    refine (cls_run_post RNGW _ mem3 (@YK11.fp_regs fx) (@YK11.fp_csr fx) spv dp bp len pos s dispc Bc B2 body j0
             ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110
             (YK11.getr regs3 (Z_to_bv 5 1)) (YK11.getr regs3 (Z_to_bv 5 5)) (YK11.getr regs3 (Z_to_bv 5 6))
             (YK11.getr regs3 (Z_to_bv 5 7)) (YK11.getr regs3 (Z_to_bv 5 11)) (YK11.getr regs3 (Z_to_bv 5 12))
             (YK11.getr regs3 (Z_to_bv 5 13)) (YK11.getr regs3 (Z_to_bv 5 14)) (YK11.getr regs3 (Z_to_bv 5 15))
             (YK11.getr regs3 (Z_to_bv 5 16)) (YK11.getr regs3 (Z_to_bv 5 17)) (YK11.getr regs3 (Z_to_bv 5 28))
             (YK11.getr regs3 (Z_to_bv 5 29)) (YK11.getr regs3 (Z_to_bv 5 30)) (YK11.getr regs3 (Z_to_bv 5 31))
             gp0 tp0 clw_bounds clw_app_sp clw_app_dp clw_off clw_rng Hlen HLB Hpos H3 Hs HTL HQR HFR Hj0 HMm _ _).
    + intros m' j y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
        y28 y29 y30 y31 Hj FRE HMm' MU WMo MG Hl0.
      eexists. split; [apply ExecF.mstepsF_refl|]. left.
      exists m', j, y1, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23,
        y24, y25, y26, y27, y28, y29, y30, y31.
      split; [reflexivity|]. split; [exact Hj|]. split; [exact FRE|]. split; [exact HMm'|].
      split; [exact MU|]. split; [exact MG | exact Hl0].
    + intros m' j0' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y24 y28 y29 y30 y31
        Hj0' FR HMm' MU WMo MG Hl0.
      eexists. split; [apply ExecF.mstepsF_refl|]. right.
      exists m', j0', y1, y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y19, y20, y21, y22, y24, y28, y29, y30,
        y31.
      split; [reflexivity|]. split; [exact Hj0'|]. split; [exact FR|]. split; [exact HMm'|].
      split; [exact MU|]. split; [exact MG | exact Hl0].
  - intros ms1 ms2 md' HP HE _ Hsb.
    destruct HP as [(m' & j & y1 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 &
                     y19 & y20 & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 &
                     -> & Hj & FRE & HMm' & MU & MG & Hl0)
                  | (m' & j0' & y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y19 & y20 & y21 &
                     y22 & y24 & y28 & y29 & y30 & y31 & -> & Hj0' & FR & HMm' & MU & MG & Hl0)].
    + (* the body is consumed: the model's loop stops, the epilogue returns *)
      destruct (cls_exit fuel B2 body len (pos + TW.Cmd_len Bc s) (Z.lor dispc (TW.Cmd_display B2 s)) Bw' disp
                  HL2 Hl0) as [EB ED].
      destruct (clw_run_step mem3 m' md3 md' HJ3 HK3 HG3 MU MG Hsb) as (HJ1 & HK1 & HG1).
      apply (clw_epi m' md' _ j y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25
               y26 y27 y28 y29 y30 y31 HJ1 HK1 HG1).
      * rewrite EB, ED. exact HMm'.
      * rewrite EB. exact HAG2.
      * exact Hj.
      * exact FRE.
      * exact HE.
    + (* the next round, at pos + t->len *)
      destruct (clw_run_step mem3 m' md3 md' HJ3 HK3 HG3 MU MG Hsb) as (HJ1 & HK1 & HG1).
      destruct (cls_round_inv_c Bc s B2 HLB HIC Hs HQR) as (HLB2 & HIC2 & _).
      apply (IH (pos + TW.Cmd_len Bc s) (Z.lor dispc (TW.Cmd_display B2 s)) B2 m' md' _ j0' y1 y5 y6 y7 y10 y11 y12
               y13 y14 y15 y16 y17 y19 y20 y21 y22 y24 y28 y29 y30 y31 HL2 ltac:(lia)).
      * split; [exact HJ1|]. split; [exact HK1|]. split; [exact HG1|]. split; [exact HMm'|].
        split; [exact HLB2|]. split; [exact HIC2 | exact HAG2].
      * exact Hj0'.
      * exact FR.
      * exact HE.
Qed.

Lemma clw_loop_all : forall fuel, clw_loop_P fuel.
Proof.
  induction fuel as [|fuel IH];
    intros pos dispc Bc m md ms j0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31
      HL Hpos HI Hj0 HFR HE; [discriminate HL|].
  destruct (cls_round fuel Bc body len pos dispc Bw' disp HL Hpos Hlen)
    as (s & B2 & H3 & HTAG & Hsdef & Hs & Hsnc & HST & HTL & HSUB & HQR & HL2).
  apply (clw_seg_tag pos dispc s Bc m md ms j0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24
           x28 x29 x30 x31 Hpos H3 HTAG Hsdef Hs Hsnc HI Hj0 HFR HE).
  intros c Hc.
  apply (clw_seg_bcmp pos dispc s Bc j0 c Hpos H3 Hs Hsnc HST HTL HSUB Hj0 Hc).
  intros c' Hc'.
  exact (clw_seg_post fuel pos dispc s Bc B2 j0 c' IH (proj1 Hpos) H3 Hs Hsnc HTL HQR HL2 Hj0 Hc').
Qed.

Lemma clw_loop : forall fuel pos dispc (Bc : list byte) (m : word -> option byte) (md : Model) (ms : machine_state)
    (j0 : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31 : word),
  TC.latest_sent_loop fuel Bc body len pos dispc = Some (Bw', disp) ->
  0 <= pos < len ->
  clw_inv m md Bc dispc ->
  length j0 = 8%nat -> clw_fr m j0 ->
  Regs6ss.ms_eqv (MS (cls_regs_head x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31
                        gp0 tp0 spv dp bp len pos)
                    (@YK11.fp_regs fx) (Z_to_bv 64 543092) (@YK11.fp_csr fx) None m (YK11.seg_rom rsegs)) ms ->
  SRr tfibsegs W (mkCfg ms md) clw_post.
Proof. intros fuel. exact (clw_loop_all fuel). Qed.

(* ---- the walk ---- *)

Lemma clw_main : SRr tfibsegs W (@cfg_at fx tfibsegs (transportb_sigma TB_check_latest_sent) regs memc mdc) clw_post.
Proof using All.
  pose proof clw_stack as (Hce & H47 & Hsp0 & HSTK0 & ECS & Hpres).
  pose proof clw_bounds as HBDS. pose proof clw_app_sp as HAPs. pose proof clw_app_dp as HAPd.
  pose proof clw_off as HOFF. pose proof clw_rng as HRNG.
  destruct clw_mem0 as (v0 & HM0).
  pose proof (clw_inv0 v0 HM0) as (HJ0 & HK0 & HG0 & HLB & HIC & HAG).
  pose proof (cls_start Bw body len Bw' disp HM) as HL0.
  pose proof (Nat2Z.is_nonneg (length body)) as Hlen0.
  rewrite clw_entry_at.
  apply (@decode_run fx W regs memc mdc 542908
    (fun ms1 =>
       (exists (m' : word -> option byte) (j : list byte)
          (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
           x28 x29 x30 x31 : word),
          ms1 = MS (Frame.mkR x1 (Z_to_bv 64 spv) gp0 tp0 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                   (@YK11.fp_regs fx) (Z_to_bv 64 543564) (@YK11.fp_csr fx) None m' (YK11.seg_rom rsegs) /\
          length j = 56%nat /\ clw_fre m' j /\ cls_mem m' Bw body dp bp len (Z_to_bv 64 0) /\
          Frame.munch (cls_W spv dp) memc m' /\ YK1b.mem_grows memc m' /\ len = 0) \/
       (exists (m' : word -> option byte) (j0 : list byte)
          (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31 : word),
          ms1 = MS (cls_regs_head x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31
                      gp0 tp0 spv dp bp len 0)
                   (@YK11.fp_regs fx) (Z_to_bv 64 543092) (@YK11.fp_csr fx) None m' (YK11.seg_rom rsegs) /\
          length j0 = 8%nat /\ clw_fr m' j0 /\ cls_mem m' Bw body dp bp len (Z_to_bv 64 0) /\
          Frame.munch (cls_W spv dp) memc m' /\ YK1b.mem_grows memc m' /\ 0 < len))).
  - unfold LCW.ms_of_regs.
    assert (ESP : YK11.getr regs (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs))
      by (unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
    assert (E10 : YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 bp) by exact H10.
    assert (E11 : YK11.getr regs (Z_to_bv 5 11) = Z_to_bv 64 len) by exact H11.
    assert (E12 : YK11.getr regs (Z_to_bv 5 12) = Z_to_bv 64 dp) by exact H12.
    rewrite ESP, E10, E11, E12.
    refine (cls_run_entry RNGW _ memc (@YK11.fp_regs fx) (@YK11.fp_csr fx) slo (spZ regs) bp len dp Bw body v0
             ra0 gp0 tp0 (YK11.getr regs (Z_to_bv 5 5)) (YK11.getr regs (Z_to_bv 5 6))
             (YK11.getr regs (Z_to_bv 5 7)) s00 s10
             (YK11.getr regs (Z_to_bv 5 13)) (YK11.getr regs (Z_to_bv 5 14)) (YK11.getr regs (Z_to_bv 5 15))
             (YK11.getr regs (Z_to_bv 5 16)) (YK11.getr regs (Z_to_bv 5 17))
             s20 s30 s40 s50 s60 s70 s80 s90 s100 s110
             (YK11.getr regs (Z_to_bv 5 28)) (YK11.getr regs (Z_to_bv 5 29)) (YK11.getr regs (Z_to_bv 5 30))
             (YK11.getr regs (Z_to_bv 5 31))
             HBDS HAPs HAPd HOFF HRNG Hlen _ clw_stk0 clw_cells0 clw_kw0 HM0 _ _).
    + lia.
    + intros m' j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
        x28 x29 x30 x31 Hj FRE HMm MU WMo MG Hl0.
      eexists. split; [apply ExecF.mstepsF_refl|]. left.
      exists m', j, x1, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23,
        x24, x25, x26, x27, x28, x29, x30, x31.
      split; [reflexivity|]. split; [exact Hj|]. split; [exact FRE|]. split; [exact HMm|].
      split; [exact MU|]. split; [exact MG | exact Hl0].
    + intros m' j0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31
        Hj0 FR HMm MU WMo MG Hl0.
      eexists. split; [apply ExecF.mstepsF_refl|]. right.
      exists m', j0, x1, x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x19, x20, x21, x22, x24, x28, x29, x30,
        x31.
      split; [reflexivity|]. split; [exact Hj0|]. split; [exact FR|]. split; [exact HMm|].
      split; [exact MU|]. split; [exact MG | exact Hl0].
  - intros ms1 ms2 md' HP HE _ Hsb.
    destruct HP as [(m' & j & x1 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 &
                     x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 &
                     -> & Hj & FRE & HMm & MU & MG & Hl0)
                  | (m' & j0 & x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x19 & x20 & x21 &
                     x22 & x24 & x28 & x29 & x30 & x31 & -> & Hj0 & FR & HMm & MU & MG & Hl0)].
    + (* len = 0: the model's loop stops at once *)
      destruct (cls_exit (Datatypes.S (Z.to_nat len)) Bw body len 0 0 Bw' disp HL0 ltac:(lia)) as [EB ED].
      destruct (clw_run_step memc m' mdc md' HJ0 HK0 HG0 MU MG Hsb) as (HJ1 & HK1 & HG1).
      apply (clw_epi m' md' _ j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31 HJ1 HK1 HG1).
      * rewrite EB, ED. exact HMm.
      * rewrite EB. exact HAG.
      * exact Hj.
      * exact FRE.
      * exact HE.
    + destruct (clw_run_step memc m' mdc md' HJ0 HK0 HG0 MU MG Hsb) as (HJ1 & HK1 & HG1).
      apply (clw_loop (Datatypes.S (Z.to_nat len)) 0 0 Bw m' md' _ j0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21
               x22 x24 x28 x29 x30 x31 HL0 ltac:(lia)).
      * split; [exact HJ1|]. split; [exact HK1|]. split; [exact HG1|]. split; [exact HMm|].
        split; [exact HLB|]. split; [exact HIC | exact HAG].
      * exact Hj0.
      * exact FR.
      * exact HE.
Qed.

End W.

Theorem transport_check_latest_sent_cg_holds :
  forall fx rc B MT, @transport_check_latest_sent_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT HCELLS HSC LAWS MTL HGX LEAF HBC.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bp len dp disp body Bw Bw'
    HJ Hra Hra4 Hgp Htp H10 H11 H12 Hsp16 Hlo Hhi Hbp Hlen HG8 HSRC HOW HBD Hdp4 HTWR HDR HDOW HDG HROM HTW HM
    HINV Hev.
  exact (@clw_main fx rc B MT HCELLS HSC LAWS MTL HGX LEAF HBC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
           regs bp len dp disp body Bw Bw' HJ Hra Hra4 Hgp Htp H10 H11 H12 Hsp16 Hlo Hhi Hbp Hlen HG8 HSRC HOW HBD
           Hdp4 HTWR HDR HDOW HDG HROM HTW HM HINV Hev).
Qed.

Print Assumptions transport_check_latest_sent_cg_holds.
