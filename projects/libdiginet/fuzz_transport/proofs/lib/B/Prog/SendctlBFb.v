(* SendctlBFb: Lemma sendctl_fb : sendctl_fb_stmt (lib/B/Prog/SendctlBCut.v), the frame-build piece of image B's
   walk of send_control, offsets +0x1ac .. +0x1b8 of the listing lib/B/Prog/DgnTransportBList.v
   (fuzz_transport.asan-ubsan 0x87080 .. 0x8708c); the twin of image A's lib/A/Prog/SendctlFb.v.

   What the code does. +0x1ac `jal diginet_frame_build` (ra = 0x87084); +0x1b0 `mv s5, a0` (s5 = n);
   +0x1b4 `bltz a0, +0x260` (n < 0 goes to the release cut); +0x1b8 `beqz s6, +0x1ec` (kp = 0 goes to the send cut,
   else the keep cut at +0x1bc). Image B's diginet_frame_build asks hp mod 4 = 0 (its UBSan alignment check of hp):
   hp = F + 128 and F mod 64 = 0.

   The four instructions are stepped one by one (YA0n.v SRr_step with YK14.v step_jal_link, step_addi_at and YK11.v
   step_blt_tk / _ft, step_beq_tk / _ft); their words and decodings are decided by vm_compute (sfb_dec_jal .. sfb_dec_beq). The callee
   diginet_frame_build is a G-form callee composed in the SAME G journal: its contract transport_diginet_frame_build_cg
   (the second callee of SendctlBCut.v sendctl_callees) is applied at the call state (the own frame live, own =
   (SENDCTL_CID, pos) :: own) through SRr_bind, with out = f = F + 32 (60 bytes oj), dst = s + 120, src = s,
   hp = F + 128, body = 0 with bb = [] (the wide premise's right disjunct) and mode = S_cfg_sum_mode Bw. Its premises:
   the registers the head left (sendctl_regs_fb), trans_out_ok of f by decode_in_fake at the call state and the cut's
   decode_rd_ok, the cut's write right and bytes of f and of the header, dst's and src's 6 bytes inside g_s's payload
   (sfb_gs_src: DgnTransportBCg.v trans_src_ok_G_range with trans_sh_any_zshadow over trans_sendctl_cells, the bytes
   visible by tw_at, garr8 by TWorldG.v tw_garr8), the empty body (trans_src_ok_null), the disjointness of f and the
   image bytes (a frame byte is not an image byte: frm_img), the count premise and the event bound.

   Its post (frame_fb_post: transport_cg_post over G_HARNESS_B) gives a0 = build_code_w [] 60 mode = sendctl_code Bw
   (SendctlBCut.v sendctl_bcw), the 60 bytes at f = sendctl_fr Bw cmd ack when the code is 60 (sendctl_build_out), and
   gx_kept_ex G_HARNESS_B of [f, f + 60), so tw_at at Bw still holds (no byte of G is a frame byte). Its acall_kept_g,
   stated at the call state, is lifted to the memories with the out cell klp put back (SendctlBCut.v
   acall_kept_g_gover: klp lies outside the callee's window and is present at both memories) and folded into the cut's
   kept fact by TransportGCg.v dk_kept_trans_nf_g, the callee's written range [f, f + 60) being bytes of the own frame
   (TransportGCg.v dkg_nf, apart from the caller's blocks and frames by dkg_nf_sep). The saved words, the frame's last
   word, the cells at kp and klp and their shadow facts are carried by the callee's kept fact (the clause above
   alloc_ceiling, the block clause, the frame clause), the shadow of klp in the machine stack or in a heap block by
   AR at the state after the call (CanKit.v can_stack_addressable / can_stack_hull, YCbq.v range_addressable_of_block /
   shadow_hull_vis_of_block). The branch on n follows SendctlBCut.v sendctl_model: on code -1 the model gives r = -1,
   f = [] and Bw' = Bw (the release cut, the cells still holding K and KL); on code 60 the send or keep cut, with the
   world still Bw (nothing has written a byte of G). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_build_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CanKit SendctlBCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb TImg TSess0 TSess.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The four instructions                                            *)
(* ------------------------------------------------------------------ *)

(* The words at +0x1ac .. +0x1b8 (0x87080 .. 0x8708c), decoded: `jal ra, 0x8b818` (0x8b818 - 0x87080 = 18328),
   `mv s5, a0`, `bltz a0, +0xac`, `beqz s6, +0x34`. *)
Lemma sfb_dec_jal : decode_any (Z_to_bv 32 0x798040ef) = Some (Jal 1 18328, 4%Z).
Proof. vm_compute. do 3 f_equal; apply bv_eq; reflexivity. Qed.
Lemma sfb_dec_mv : decode_any (Z_to_bv 32 0x50a93) = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_compute. do 3 f_equal; apply bv_eq; reflexivity. Qed.
Lemma sfb_dec_blt : decode_any (Z_to_bv 32 0x0a054663) = Some (Branch BC_LT 10 0 172, 4%Z).
Proof. vm_compute. do 3 f_equal; apply bv_eq; reflexivity. Qed.
Lemma sfb_dec_beq : decode_any (Z_to_bv 32 0x020b0a63) = Some (Branch BC_EQ 22 0 52, 4%Z).
Proof. vm_compute. do 3 f_equal; apply bv_eq; reflexivity. Qed.

(* `count_cid` of a frame list that starts with a frame of the class. *)
Lemma sfb_count_cons : forall c p l, count_cid c ((c, p) :: l) = 1 + count_cid c l.
Proof. intros c p l. cbn [count_cid]. rewrite Z.eqb_refl. reflexivity. Qed.

(* rdword reads its eight bytes only. *)
Lemma sfb_rdword_kept : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H.
assert (H0 : rd' a = rd a) by (rewrite <- (Z.add_0_r a); apply H; lia).
unfold rdword. rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma sfb_hull_81_inv : forall q s, q mod 8 = 0 ->
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + 1 - 1) / 8 * 8 + 8 ->
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + 8 - 1) / 8 * 8 + 8.
Proof.
intros q s Hq Hs. replace (q + 1 - 1) with q in Hs by lia.
assert (E : (q + 8 - 1) / 8 = q / 8).
{ pose proof (Z.div_mod q 8 ltac:(lia)) as D. rewrite Hq, Z.add_0_r in D.
  replace (q + 8 - 1) with (q / 8 * 8 + 7) by lia. rewrite Z.div_add_l by lia.
  change (7 / 8) with 0. lia. }
unfold shadow_addr in *. rewrite E. exact Hs.
Qed.

(* The hull of the 8 bytes of one granule is the hull of its first byte. *)
Lemma sfb_hull_81 : forall q s, q mod 8 = 0 ->
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + 8 - 1) / 8 * 8 + 8 ->
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + 1 - 1) / 8 * 8 + 8.
Proof.
intros q s Hq Hs. replace (q + 1 - 1) with q by lia.
assert (E : (q + 8 - 1) / 8 = q / 8).
{ pose proof (Z.div_mod q 8 ltac:(lia)) as D. rewrite Hq, Z.add_0_r in D.
  replace (q + 8 - 1) with (q / 8 * 8 + 7) by lia. rewrite Z.div_add_l by lia.
  change (7 / 8) with 0. lia. }
unfold shadow_addr in *. rewrite E in Hs. exact Hs.
Qed.
Lemma sfb_hull_18 : forall rd q, q mod 8 = 0 -> shadow_hull_vis rd q 1 -> shadow_hull_vis rd q 8.
Proof. intros rd q Hq H s Hs. apply H. exact (sfb_hull_81 q s Hq Hs). Qed.

(* The out cells of send_control's post. *)
Lemma sfb_outs_in : forall kp klp a, inG (sendctl_outs kp klp) a -> kp <> 0 /\ klp <= a < klp + 8.
Proof.
intros kp klp a. unfold sendctl_outs. destruct (Z.eqb_spec kp 0) as [E|E]; intros H.
- exfalso. exact (inG_nil a H).
- split; [exact E|]. apply inG_cons in H as [H|H]; [unfold in_zr in H; cbn [fst snd] in H; lia|].
  exfalso. exact (inG_nil a H).
Qed.

(* A write right of the caller's journal moves to a state with more blocks, more own frames and the same frame
   base. *)
Lemma sfb_awr_move : forall STK sp0 FP bl0 blc blc' (ly ly' : alayout) own own' a,
  awr_byte STK sp0 FP bl0 blc ly own a ->
  (forall bm, In bm blc -> In bm blc') -> ly_F ly' = ly_F ly -> (forall c, In c own -> In c own') ->
  awr_byte STK sp0 FP bl0 blc' ly' own' a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own own' a
  [H | [(Hf & b & n & Hin & Hb) | [(b & n & Hin & Hn0 & Hb) | (c & p & Hc & Hr)]]] Hbl EF Hown.
- left. exact H.
- right. left. split; [exact Hf|]. exists b, n. split; [exact (Hbl _ Hin) | exact Hb].
- right. right. left. exists b, n. split; [exact (Hbl _ Hin)|]. split; [exact Hn0 | exact Hb].
- right. right. right. exists c, p. split; [exact (Hown _ Hc)|]. unfold frame_addr in *. rewrite EF. exact Hr.
Qed.

Section fb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma sfb_fetch : forall k w, clookup (@pa_tbl _ transportb_listing PI_transportb) (BASE + k) = Some w ->
  fetch_word segs (Z_to_bv 64 (BASE + k)) = Some (Z_to_bv 32 w).
Proof. intros k w H. exact (pa_fetch_ok (PI := PI_transportb) _ _ H). Qed.

(* +0x1ac `jal diginet_frame_build`. *)
Lemma sfb_step_jal : forall regs mem rom,
  RiscvSemantics.step segs (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SENDCTL_FB)) mem rom) =
  MachineOk (@YK11.mkst fx (YK11.regupd regs 1 (Z_to_bv 64 (BASE + (SENDCTL_FB + 4))))
    (Z_to_bv 64 (transportb_sigma TB_diginet_frame_build)) mem rom).
Proof.
intros regs mem rom.
rewrite (step_jal_link segs regs _ mem rom _ 1 18328 (sfb_fetch SENDCTL_FB 0x798040ef ltac:(vm_compute; reflexivity))
  ltac:(vm_compute; reflexivity) sfb_dec_jal).
assert (E1 : v_addi (Z_to_bv 64 (BASE + SENDCTL_FB)) 4 = Z_to_bv 64 (BASE + (SENDCTL_FB + 4)))
  by (vm_compute; reflexivity).
assert (E2 : btgt (Z_to_bv 64 (BASE + SENDCTL_FB)) (bv_signed (18328 : bv 21)) =
  Z_to_bv 64 (transportb_sigma TB_diginet_frame_build)) by (vm_compute; reflexivity).
rewrite E1, E2. reflexivity.
Qed.

(* +0x1b0 `mv s5, a0`. *)
Lemma sfb_step_mv : forall regs mem rom,
  RiscvSemantics.step segs (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (SENDCTL_FB + 4))) mem rom) =
  MachineOk (@YK11.mkst fx (YK11.regupd regs 21 (YK11.getr regs 10)) (Z_to_bv 64 (BASE + (SENDCTL_FB + 8))) mem rom).
Proof.
intros regs mem rom.
assert (Hv : v_addi (YK11.getr regs 10) (bv_signed (0%bv : bv 12)) = YK11.getr regs 10).
{ unfold v_addi. change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. }
rewrite (step_addi_at segs regs _ mem rom _ 21 10 0 _
  (sfb_fetch (SENDCTL_FB + 4) 0x50a93 ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) sfb_dec_mv
  eq_refl Hv).
assert (E1 : v_addi (Z_to_bv 64 (BASE + (SENDCTL_FB + 4))) 4 = Z_to_bv 64 (BASE + (SENDCTL_FB + 8)))
  by (vm_compute; reflexivity).
rewrite E1. reflexivity.
Qed.

(* +0x1b4 `bltz a0, +0x260`. *)
Lemma sfb_step_blt_tk : forall regs mem rom, bv_lts (YK11.getr regs 10) (Z_to_bv 64 0) = true ->
  RiscvSemantics.step segs (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (SENDCTL_FB + 8))) mem rom) =
  MachineOk (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SENDCTL_REL)) mem rom).
Proof.
intros regs mem rom H.
rewrite (step_blt_tk segs regs _ mem rom _ 10 0 172
  (sfb_fetch (SENDCTL_FB + 8) 0x0a054663 ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) sfb_dec_blt H).
assert (E1 : btgt (Z_to_bv 64 (BASE + (SENDCTL_FB + 8))) (bv_signed (172%bv : bv 13)) = Z_to_bv 64 (BASE + SENDCTL_REL))
  by (vm_compute; reflexivity).
rewrite E1. reflexivity.
Qed.
Lemma sfb_step_blt_ft : forall regs mem rom, bv_lts (YK11.getr regs 10) (Z_to_bv 64 0) = false ->
  RiscvSemantics.step segs (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (SENDCTL_FB + 8))) mem rom) =
  MachineOk (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (SENDCTL_FB + 12))) mem rom).
Proof.
intros regs mem rom H.
rewrite (step_blt_ft segs regs _ mem rom _ 10 0 172
  (sfb_fetch (SENDCTL_FB + 8) 0x0a054663 ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) sfb_dec_blt H).
assert (E1 : v_addi (Z_to_bv 64 (BASE + (SENDCTL_FB + 8))) 4 = Z_to_bv 64 (BASE + (SENDCTL_FB + 12)))
  by (vm_compute; reflexivity).
rewrite E1. reflexivity.
Qed.

(* +0x1b8 `beqz s6, +0x1ec`. *)
Lemma sfb_step_beq_tk : forall regs mem rom, bv_eqb (YK11.getr regs 22) (Z_to_bv 64 0) = true ->
  RiscvSemantics.step segs (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (SENDCTL_FB + 12))) mem rom) =
  MachineOk (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SENDCTL_SEND)) mem rom).
Proof.
intros regs mem rom H.
rewrite (step_beq_tk segs regs _ mem rom _ 22 0 52
  (sfb_fetch (SENDCTL_FB + 12) 0x020b0a63 ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) sfb_dec_beq H).
assert (E1 : btgt (Z_to_bv 64 (BASE + (SENDCTL_FB + 12))) (bv_signed (52%bv : bv 13)) = Z_to_bv 64 (BASE + SENDCTL_SEND))
  by (vm_compute; reflexivity).
rewrite E1. reflexivity.
Qed.
Lemma sfb_step_beq_ft : forall regs mem rom, bv_eqb (YK11.getr regs 22) (Z_to_bv 64 0) = false ->
  RiscvSemantics.step segs (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (SENDCTL_FB + 12))) mem rom) =
  MachineOk (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SENDCTL_KEEP)) mem rom).
Proof.
intros regs mem rom H.
rewrite (step_beq_ft segs regs _ mem rom _ 22 0 52
  (sfb_fetch (SENDCTL_FB + 12) 0x020b0a63 ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) sfb_dec_beq H).
assert (E1 : v_addi (Z_to_bv 64 (BASE + (SENDCTL_FB + 12))) 4 = Z_to_bv 64 (BASE + SENDCTL_KEEP))
  by (vm_compute; reflexivity).
rewrite E1. reflexivity.
Qed.

(* One step of the machine, the model materialized. *)
Lemma sfb_srr_step : forall (W : world segs) regs pc mem regs' pc' md Q,
  (forall rom (m : word -> option byte),
     RiscvSemantics.step segs (@YK11.mkst fx regs pc m rom) = MachineOk (@YK11.mkst fx regs' pc' m rom)) ->
  (forall mat, SRr segs W (mkCfg (@YK11.mkst fx regs' pc' mem (YK11.seg_rom segs))
     (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs pc mem (YK11.seg_rom segs)) md) Q.
Proof.
intros W regs pc mem regs' pc' md Q Hst HK.
eapply (SRr_step segs (@pa_wx _ _ PI_transportb) W); [reflexivity | rewrite restrict_mkst_fx; apply Hst |].
intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
cbn [ms_regs ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict. apply HK.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Facts of the memories                                            *)
(* ------------------------------------------------------------------ *)

(* g_s's payload bytes are bytes of G. *)
Lemma sfb_gs_inG : forall a, SENDCTL_S <= a < SENDCTL_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr. cbn [fst snd]. unfold SENDCTL_S, TB_g_s, TW.SZ_g_s in Ha. lia.
Qed.

(* A range of g_s's payload whose 64-byte blocks lie in g_s: diginet_frame_build's source placement. *)
Lemma sfb_gs_src : forall lyc Sc (W : world segs) mem md Bw q n,
  trans_sendctl_cells B -> @AR rc segs B lyc Sc W mem md -> tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  0 < n -> SENDCTL_S <= q -> q + n <= SENDCTL_S + TW.SZ_g_s ->
  SENDCTL_S <= q / 64 * 64 -> (q + n - 1) / 64 * 64 + 64 <= SENDCTL_S + TW.SZ_g_s ->
  trans_src_ok B lyc Sc W mem q n.
Proof.
intros lyc Sc W mem md Bw q n HZ HAR Htw Hn H1 H2 H3 H4.
pose proof (trans_sh_any_zshadow B _ _ q n HZ Hn H3 H4) as Hsh.
apply (trans_src_ok_G_range B lyc Sc W mem q n 0x5df640 18264).
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold SENDCTL_S, TB_g_s in H1. lia.
- unfold SENDCTL_S, TB_g_s, TW.SZ_g_s in H2. lia.
- exact Hsh.
- destruct (Hsh lyc Sc W mem md HAR) as [Ha Hh].
  split; [|split; [exact Ha | split; [exact Hh|]]].
  + intros a Ha'. destruct Htw as [_ Hrow].
    replace a with (TB_g_s + (a - TB_g_s)) by lia.
    rewrite (Hrow TW.OFF_g_s TB_g_s TW.SZ_g_s (a - TB_g_s) TMAP_B_g_s
      ltac:(unfold SENDCTL_S, TB_g_s, TW.SZ_g_s in *; lia)).
    discriminate.
  + unfold amem_range, kLowMemEnd. unfold SENDCTL_S, TB_g_s, TW.SZ_g_s in *. lia.
Qed.

(* The cells a callee keeps keep their values. *)
Lemma sfb_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) q (l : list Z),
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (q + j) = aview segs H m (q + j)) ->
  garr8 segs (mrestrict H m) q l -> garr8 segs (mrestrict H' m') q l.
Proof.
intros H H' m m' q l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
apply (val_mem_kept segs H H' m m' (q + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros i Hi. change (Z.of_nat 1) with 1 in Hi. replace (q + Z.of_nat j + i) with (q + Z.of_nat j) by lia.
apply Hk. lia.
Qed.

(* The bytes garr8 describes are visible. *)
Lemma sfb_garr8_vis : forall (H : word -> bool) (m : word -> option byte) q (l : list Z) a,
  garr8 segs (mrestrict H m) q l -> q <= a < q + Z.of_nat (length l) -> aview segs H m a <> None.
Proof.
intros H m q l a Hg Ha.
assert (Hj : (Z.to_nat (a - q) < length l)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; lia).
replace a with (q + Z.of_nat (Z.to_nat (a - q))) by (rewrite Z2Nat.id by lia; lia).
unfold aview. rewrite (garr8_mbyte segs _ q l _ Hg Hj). discriminate.
Qed.

(* decode_rd_ok of a range of one of the caller's frames at a later memory whose bytes there are visible and whose
   frames' shadow bytes are kept (DgnTransportCg.v decode_rd_ok_fake_kept, with the range's bytes visible instead of
   kept: the callee wrote them). *)
Lemma sfb_rd_ok_fake : AR_laws segs B -> forall lyc Sc (W W' : world segs) memc mem' mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> decode_in_fake lyc Sc q n -> decode_rd_ok W memc q n -> 0 < n ->
  (forall a, q <= a < q + n -> aview segs (w_H W') mem' a <> None) ->
  (forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W') mem' s = aview segs (w_H W) memc s) ->
  decode_rd_ok W' mem' q n.
Proof.
intros LAWS lyc Sc W W' memc mem' mdc q n HAR (cid & pos & Hin & F1 & F2) (R1 & R2 & R3 & R4 & R5 & R6) Hn K1 K2.
assert (AL : frame_addr lyc cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid)
  by exact (TransportGCg.dkg_frame_al64 segs B lyc Sc W memc mdc cid pos HAR Hin).
destruct AL as (A1 & A2 & A3).
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (B1 & B2 & _).
assert (KG : forall g, frame_addr lyc cid pos <= g < frame_addr lyc cid pos + fs_frame_bytes cid ->
  aview segs (w_H W') mem' (shadow_addr g) = aview segs (w_H W) memc (shadow_addr g)).
{ intros g Hg. apply (K2 cid pos); [exact Hin|]. unfold in_zr, shadow_addr. cbn [fst snd].
  pose proof (Z.div_mod (frame_addr lyc cid pos) 64 ltac:(lia)).
  pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)).
  pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (frame_addr lyc cid pos) 8 ltac:(lia)).
  pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
  pose proof (Z.div_mod g 8 ltac:(lia)). pose proof (Z.mod_pos_bound g 8 ltac:(lia)). lia. }
split; [|split; [|split; [|exact (conj R4 (conj R5 R6))]]].
- exact K1.
- intros x Hx. destruct (R2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs |- *.
  rewrite (KG x ltac:(lia)). exact Hs.
- intros s Hs.
  assert (Hhi : (frame_addr lyc cid pos + fs_frame_bytes cid) mod 64 = 0)
    by (rewrite Z.add_mod, A1, A2 by lia; reflexivity).
  destruct (YG0s.hull_inside (frame_addr lyc cid pos) (frame_addr lyc cid pos + fs_frame_bytes cid) q n s
    A1 Hhi ltac:(lia) F1 F2 ltac:(lia) Hs) as (g & Hg8 & Hgr & ->).
  rewrite (KG g Hgr). exact (R3 _ Hs).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Lemma sendctl_fb : @sendctl_fb_stmt fx rc B MT.
Proof.
unfold sendctl_fb_stmt. intros KEEP SEND REL.
unfold sendctl_fb_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw Bw'
  pos sp1 F S2 mem2 md2 oj regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (_ & _ & HSC & HROU & HRNE & LAWS & MTL & MTF & _ & _ & FFL & HGX & _).
pose proof CALLEES as (_ & FBC & _ & _).
pose proof HFIX as (HJ0 & Hret & _ & Hgp & Htp & _ & _ & _ & _ & _ & Hsp16 & Hstk & Hsp0 & Hcmd & Hack & HKP & HTW0 &
  Hgf & HM & _ & _ & _ & Hcnt & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
destruct HCUR as ((HJ1 & _ & Hfrs & _ & _ & Hmo & HK & Hsaved & HFLw & HKLP) & Eab & HTW & HROM & Loj & Goj & Roj &
  TWoj & Ghdr & Rhdr & INC).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R10 & R11 &
  R12 & R13 & R14 & R15 & R16 & R17).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESTK : SENDCTL_STK = 8656) by reflexivity.
assert (FSTK : FRAME_FB_STK = 4368) by reflexivity.
assert (FFR : FRAME_FB_FRAME = 96) by reflexivity.
assert (EV0 : SENDCTL_EV = 0) by reflexivity.
assert (FEV0 : FRAME_FB_EV = 0) by reflexivity.
assert (LOJ : length oj = 60%nat) by exact Loj.
assert (ZLOJ : Z.of_nat (length oj) = 60) by (rewrite LOJ; reflexivity).
unfold SENDCTL_FBYTES in HFc, HFapp. unfold SENDCTL_FRAME in Esp1.
(* the caller's stack window lies above alloc_ceiling, below 2 ^ 47 *)
pose proof HJ0 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HARc & HlyC & _ & _ & _ & HfrsC & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HlyC as (_ & _ & _ & _ & _ & ELFc & _ & _ & _ & ESLc & ESHc & _).
clear HJi memS.
pose proof (bv_unsigned_in_range 64 (YK11.getr regs (Z_to_bv 5 2))) as Hsp64.
change (bv_modulus 64) with (2 ^ 64) in Hsp64. fold (spZ regs) in Hsp64.
assert (Hsp1 : spZ regs - 160 < sp1 <= spZ regs - 128 /\ sp1 mod 32 = 0).
{ rewrite Esp1. pose proof (Z.div_mod (spZ regs - 128) 32 ltac:(lia)).
  pose proof (Z.mod_pos_bound (spZ regs - 128) 32 ltac:(lia)).
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult. }
destruct Hsp1 as (Hsp1 & Hsp132).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR2.
assert (Hin2 : In (SENDCTL_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFB : fs_frame_bytes SENDCTL_CID = 256) by reflexivity.
set (FL := flag_addr lyc SENDCTL_CID pos) in *.
destruct (dkg_nf_sep segs B LAWS transportb_segs_low lyc Sc S2 W mem2 md2 SENDCTL_CID pos F FL HAR2 Hfrs Eab EF
  eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (FIMG : forall a, F <= a < F + 256 -> ~ in_img segs a).
{ intros a Ha. apply (frm_img segs B LAWS lyc S2 W mem2 md2 SENDCTL_CID pos a HAR2 Hin2).
  rewrite <- EF, EFB. exact Ha. }
assert (EN : forall a, F + SENDCTL_FOFF <= a < F + SENDCTL_FOFF + Z.of_nat (length oj) ->
  dkg_nf SENDCTL_CID F FL a).
{ intros a Ha. left. rewrite EFB. rewrite ZLOJ in Ha. unfold SENDCTL_FOFF in Ha. lia. }
(* +0x1ac: `jal diginet_frame_build` *)
apply (sfb_srr_step W regs2 _ mem2 _ _ md2 _ (fun rom m => sfb_step_jal regs2 m rom)).
intros mat1.
pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ1)
  as HJ1'.
set (md2' := with_vm_backing (m_vm_lazy md2) mat1 md2) in *. clearbody md2'.
set (regs3 := YK11.regupd regs2 1 (Z_to_bv 64 (BASE + (SENDCTL_FB + 4)))).
assert (G1 : YK11.getr regs3 1 = Z_to_bv 64 (BASE + (SENDCTL_FB + 4))) by (apply getr_same; reg_neq_tac).
assert (G2 : YK11.getr regs3 2 = w64 sp1) by (unfold regs3; rewrite getr_other by reg_neq_tac; exact R2).
assert (SP3 : spZ regs3 = sp1).
{ unfold spZ. transitivity (bv_unsigned (w64 sp1)); [f_equal; exact G2 | apply unsigned_lit_small; lia]. }
(* the callee's contract at the call state *)
eapply SRr_bind.
{ apply (FBC fx STK sp0 FP ly S W0 mem0 md0 ((SENDCTL_CID, pos) :: own) lyc S2 W mem2 md2' (k + 0) regs3
    (F + SENDCTL_FOFF) (SENDCTL_S + 120) SENDCTL_S (F + SENDCTL_HOFF) 0 (TW.S_cfg_sum_mode Bw)
    (TW.S_host_counter Bw) ack 0 cmd 0 (TW.S_desk_mac Bw) (TW.S_cfg_host_mac Bw) [] oj).
  - exact HJ1'.
  - rewrite G1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold SENDCTL_FB, AF_send_control; lia | reflexivity].
  - assert (ERA : raZ regs3 = 553092).
    { unfold raZ. transitivity (bv_unsigned (Z_to_bv 64 (BASE + (SENDCTL_FB + 4)))); [f_equal; exact G1|].
      vm_compute. reflexivity. }
    rewrite ERA. lia.
  - unfold regs3. rewrite getr_other by reg_neq_tac. rewrite R3. exact Hgp.
  - unfold regs3. rewrite getr_other by reg_neq_tac. rewrite R4. exact Htp.
  - unfold regs3. rewrite getr_other by reg_neq_tac. exact R10.
  - unfold regs3. rewrite getr_other by reg_neq_tac. rewrite ZLOJ. exact R11.
  - unfold regs3. rewrite getr_other by reg_neq_tac. exact R12.
  - unfold regs3. rewrite getr_other by reg_neq_tac. exact R13.
  - unfold regs3. rewrite getr_other by reg_neq_tac. exact R14.
  - unfold regs3. rewrite getr_other by reg_neq_tac. exact R15.
  - unfold regs3. rewrite getr_other by reg_neq_tac. exact R16.
  - unfold regs3. rewrite getr_other by reg_neq_tac. exact R17.
  - rewrite SP3. rewrite <- (Z_mod_mult (sp1 / 32 * 2) 16). f_equal.
    pose proof (Z.div_mod sp1 32 ltac:(lia)). lia.
  - rewrite SP3, FSTK. rewrite ESTK in Hstk. lia.
  - rewrite SP3. lia.
  - unfold SENDCTL_FOFF. lia.
  - unfold SENDCTL_S, TB_g_s. lia.
  - unfold SENDCTL_S, TB_g_s. lia.
  - unfold SENDCTL_HOFF. lia.
  - right. reflexivity.
  - (* image B: hp = F + 128 is 4-aligned *)
    unfold SENDCTL_HOFF. pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
    rewrite DF. replace (64 * (F / 64) + 128) with ((16 * (F / 64) + 32) * 4) by lia. apply Z_mod_mult.
  - exact (TWL.s32_range Bw TW.A_S_cfg_sum_mode).
  - pose proof (TWL.u_at_range Bw TW.A_S_host_counter 4) as Hu. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hu.
    exact Hu.
  - exact Hack.
  - lia.
  - exact Hcmd.
  - lia.
  - (* f: in the own frame, readable *)
    rewrite ZLOJ. split; [|exact Roj]. left. exists SENDCTL_CID, pos. split; [exact Hin2|].
    rewrite <- EF, EFB. unfold SENDCTL_FOFF. lia.
  - rewrite SP3, ZLOJ. exact TWoj.
  - exact Goj.
  - unfold TW.S_desk_mac. apply TWL.length_sub; [unfold TW.A_S_desk_mac, TW.OFF_g_s; lia|].
    rewrite (tw_len _ _ _ HTW). unfold TW.A_S_desk_mac, TW.OFF_g_s, TW.W_LEN. lia.
  - apply (sfb_gs_src lyc S2 W mem2 md2 Bw (SENDCTL_S + 120) 6 HSC HAR2 HTW);
      [lia | lia | | | ]; apply Z.leb_le; vm_compute; reflexivity.
  - left. rewrite SP3, FSTK. unfold SENDCTL_S, TB_g_s. rewrite ESTK in Hstk. lia.
  - exact (tw_garr8 segs (mrestrict (w_H W) mem2) TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 120 6 TMAP_B_ok HTW
      TMAP_B_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  - unfold TW.S_cfg_host_mac. apply TWL.length_sub; [unfold TW.A_S_cfg_host_mac, TW.OFF_g_s; lia|].
    rewrite (tw_len _ _ _ HTW). unfold TW.A_S_cfg_host_mac, TW.OFF_g_s, TW.W_LEN. lia.
  - apply (sfb_gs_src lyc S2 W mem2 md2 Bw SENDCTL_S 6 HSC HAR2 HTW);
      [lia | lia | | | ]; apply Z.leb_le; vm_compute; reflexivity.
  - left. rewrite SP3, FSTK. unfold SENDCTL_S, TB_g_s. rewrite ESTK in Hstk. lia.
  - pose proof (tw_garr8 segs (mrestrict (w_H W) mem2) TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 0 6 TMAP_B_ok HTW
      TMAP_B_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as HG.
    rewrite Z.add_0_r in HG. exact HG.
  - exact (trans_src_ok_null B lyc S2 W mem2).
  - left. rewrite SP3, FSTK. rewrite ESTK in Hstk. cbn [length Z.of_nat]. lia.
  - apply garr8_nil.
  - exists SENDCTL_CID, pos. split; [exact Hin2|]. rewrite <- EF, EFB. unfold SENDCTL_HOFF. lia.
  - exact Rhdr.
  - left. rewrite SP3, FSTK. rewrite ESTK in Hstk. unfold SENDCTL_HOFF. lia.
  - exact Ghdr.
  - rewrite ZLOJ.
    destruct (Z_le_gt_dec (F + SENDCTL_FOFF + 60) (SENDCTL_S + 120)) as [h|h]; [left; exact h|]. right.
    destruct (Z_le_gt_dec (SENDCTL_S + 120 + 6) (F + SENDCTL_FOFF)) as [h2|h2]; [exact h2|]. exfalso.
    apply (FIMG (Z.max (F + SENDCTL_FOFF) (SENDCTL_S + 120))).
    + unfold SENDCTL_FOFF in *. lia.
    + apply trans_g_img. apply sfb_gs_inG. unfold SENDCTL_FOFF, SENDCTL_S, TB_g_s, TW.SZ_g_s in *. lia.
  - rewrite ZLOJ.
    destruct (Z_le_gt_dec (F + SENDCTL_FOFF + 60) SENDCTL_S) as [h|h]; [left; exact h|]. right.
    destruct (Z_le_gt_dec (SENDCTL_S + 6) (F + SENDCTL_FOFF)) as [h2|h2]; [exact h2|]. exfalso.
    apply (FIMG (Z.max (F + SENDCTL_FOFF) SENDCTL_S)).
    + unfold SENDCTL_FOFF in *. lia.
    + apply trans_g_img. apply sfb_gs_inG. unfold SENDCTL_FOFF, SENDCTL_S, TB_g_s, TW.SZ_g_s in *. lia.
  - left. rewrite ZLOJ. unfold SENDCTL_FOFF, SENDCTL_HOFF. lia.
  - right. cbn [length Z.of_nat]. unfold SENDCTL_FOFF. lia.
  - rewrite <- sendctl_cid_bc, Hfrs, sfb_count_cons. lia.
  - rewrite FEV0. rewrite EV0 in Hev. lia. }
(* +0x1b0: the return from diginet_frame_build *)
cbv beta. intros W2 c2 _ HPOST.
unfold frame_fb_post, transport_cg_post in HPOST.
destruct HPOST as (ly3 & S3 & regs4 & mem4 & md4 & e & -> & He & HJ4 & HP4 & Hfr4 & Hperm4 & HK4 & Hmo4 & X10 & Xout &
  Xgx).
assert (E0 : e = 0) by (rewrite FEV0 in He; lia). subst e.
replace (k + 0 + 0) with (k + 0) in HJ4 by lia.
rewrite G1.
rewrite SP3 in HK4.
rewrite (sendctl_bcw Bw oj LOJ) in X10.
pose proof HJ4 as (_ & _ & (memS4 & HJ4i & _) & _). rewrite !Z.add_0_r in HJ4i.
pose proof HJ4i as (HAR4 & Hly4 & _).
pose proof Hly4 as (_ & _ & _ & _ & _ & ELF4 & _ & _ & _ & ESL4 & ESH4 & _).
assert (ELF : ly_F ly3 = ly_F lyc) by (rewrite ELF4, ELFc; reflexivity).
assert (BL3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3)).
{ intros bm Hbm. apply (Permutation_in _ (Permutation_sym Hperm4)). rewrite Eab. exact Hbm. }
assert (FR3 : frames S3 = (SENDCTL_CID, pos) :: frames Sc) by (rewrite Hfr4; exact Hfrs).
destruct HK4 as (K1 & K2 & K3 & K4 & K5 & K6).
(* what the callee keeps: every byte the caller's journal lets a callee write, outside the callee's window *)
assert (KAW : forall a, awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  ~ (sp1 - FRAME_FB_STK <= a < sp1) -> aview segs (w_H W2) mem4 a = aview segs (w_H W) mem2 a).
{ intros a Hw Hn. destruct Hw as [Hw | [(_ & b & m & Hb & Hr) | [(b & m & Hb & _ & Hr) | (c0 & p0 & Hc & Hr)]]].
  - apply K1; [lia | exact Hn].
  - replace a with (b + (a - b)) by lia.
    apply (K2 b m (a - b)); [rewrite Eab; exact Hb | lia|].
    intros HE. apply (N1 b m (a - b) Hb ltac:(lia)). apply EN. exact HE.
  - replace a with (b + (a - b)) by lia.
    apply (K2 b m (a - b)); [rewrite Eab; exact Hb | lia|].
    intros HE. apply (N1 b m (a - b) Hb ltac:(lia)). apply EN. exact HE.
  - assert (Hc' : In (c0, p0) (frames Sc)) by (rewrite HfrsC; apply in_or_app; left; exact Hc).
    apply (K4 c0 p0 a); [rewrite Hfrs; right; exact Hc' | exact Hr|].
    intros HE. exact (N3 c0 p0 a Hc' Hr (EN a HE)). }
(* the shadow bytes of the call state's frames are kept *)
assert (KSH : forall c p s, In (c, p) (frames S2) ->
  in_zr s (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8) ->
  aview segs (w_H W2) mem4 s = aview segs (w_H W) mem2 s).
{ intros c p s Hcp Hs. apply (K4 c p s Hcp (or_intror Hs)). intros HE.
  rewrite Hfrs in Hcp. destruct Hcp as [Heq | Hcp'].
  - destruct (proj1 (pair_equal_spec _ _ _ _) Heq) as [Hc Hp]. subst c p. unfold in_zr in Hs. cbn [fst snd] in Hs. rewrite <- EF, EFB in Hs.
    rewrite ZLOJ in HE. unfold SENDCTL_FOFF in HE. unfold shadow_addr, SHADOW_OFF in Hs.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia.
  - exact (N3 c p s Hcp' (or_intror Hs) (EN s HE)). }
(* the out cell klp: outside the callee's window, present at both memories *)
assert (PKL : kp = 0 \/ (forall i, 0 <= i < 8 -> apresent (w_H W2) mem4 (klp + i))).
{ destruct HKP as [Hk0 | (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TWKL & _ & _ & NGKL & _)]; [left; exact Hk0|].
  right. intros i Hi.
  destruct (TWKL (klp + i) ltac:(lia)) as [(Hw & _) | HG]; [|exfalso; exact (NGKL (klp + i) ltac:(lia) HG)].
  apply (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ ly3 S3 W2 mem4 md4 _ _ HJ4i).
  apply (sfb_awr_move _ _ _ _ _ _ lyc ly3 own _ _ Hw BL3 ELF). intros c Hc. right. exact Hc. }
assert (Hout4 : forall a, inG (sendctl_outs kp klp) a ->
  0 <= a < 2 ^ 64 /\ ~ (sp1 - FRAME_FB_STK <= a < sp1) /\ apresent (w_H W) mem2 a /\
  apresent (w_H W2) mem4 a /\ apresent (w_H W) memc a).
{ intros a Ha. destruct (sfb_outs_in kp klp a Ha) as (Hkp & Hr).
  destruct HKP as [Hk0 | (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TWKL & RDKL & OWKL & NGKL & _)];
    [exfalso; exact (Hkp Hk0)|].
  destruct HKLP as [Hk0 | HPK]; [exfalso; exact (Hkp Hk0)|].
  destruct PKL as [Hk0 | HPK4]; [exfalso; exact (Hkp Hk0)|].
  destruct RDKL as (_ & _ & _ & _ & Hklp0 & Hklpn).
  split; [lia|]. split; [unfold decode_off_win in OWKL; rewrite ESTK, FSTK in *; lia|].
  split; [replace a with (klp + (a - klp)) by lia; apply HPK; lia|].
  split; [replace a with (klp + (a - klp)) by lia; apply HPK4; lia|].
  destruct (TWKL a Hr) as [(_ & Hp & _) | HG]; [exact Hp | exfalso; exact (NGKL a Hr HG)]. }
pose proof (acall_kept_g_gover B TG.G_HARNESS_B (sendctl_outs kp klp) lyc S2 W W2 mem2 mem4 memc md2
  (sp1 - FRAME_FB_STK) sp1 _ LAWS HAR2 ltac:(rewrite FSTK, ESTK in *; lia) ltac:(lia) Hout4
  (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 K6)))))) as HK4g.
assert (KEPT : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (gover (sendctl_outs kp klp) mem4 memc)
  (spZ regs - SENDCTL_STK) (spZ regs) (sendctl_wr kp klp)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc lyc S2 W memc W (gover (sendctl_outs kp klp) mem2 memc) W2
    (gover (sendctl_outs kp klp) mem4 memc) (spZ regs - SENDCTL_STK) (spZ regs) (sp1 - FRAME_FB_STK) sp1
    (sendctl_wr kp klp) (fun a => F + SENDCTL_FOFF <= a < F + SENDCTL_FOFF + Z.of_nat (length oj))
    (dkg_nf SENDCTL_CID F FL)).
  - rewrite ESTK in *. lia.
  - lia.
  - intros; reflexivity.
  - intros f0 Hf0. rewrite Hfrs. right. exact Hf0.
  - intros bm Hbm. rewrite Eab. exact Hbm.
  - exact N1.
  - exact N3.
  - exact HK.
  - exact HK4g.
  - rewrite FSTK, ESTK in *. lia.
  - lia.
  - intros a Ha. right. exact (EN a Ha). }
(* the saved words and the frame's last word *)
assert (SAV : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem4) (spZ regs - fst o) =
  Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SENDCTL_SAVED).
{ apply Forall_forall. intros o Hoin. pose proof (proj1 (Forall_forall _ _) Hsaved o Hoin) as Ho. cbv beta in Ho.
  assert (Hob : 8 <= fst o <= 96).
  { unfold SENDCTL_SAVED in Hoin. cbn [In] in Hoin.
    repeat (destruct Hoin as [<- | Hoin]; [cbn [fst]; lia|]). destruct Hoin. }
  rewrite <- Ho. apply sfb_rdword_kept. intros i Hi. apply K1; [rewrite ESTK in *; lia | rewrite FSTK; lia]. }
assert (FLW : rdword (aview segs (w_H W2) mem4) (F + SENDCTL_FBYTES - 8) = Some FL).
{ rewrite <- HFLw. apply sfb_rdword_kept. intros i Hi. apply (K4 SENDCTL_CID pos); [exact Hin2| |].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF, EFB. unfold SENDCTL_FBYTES. lia.
  - intros HE. cbv beta in HE. rewrite ZLOJ in HE. unfold SENDCTL_FOFF, SENDCTL_FBYTES in *. lia. }
(* the cut's facts at the state after the call *)
assert (CURm : forall md, @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((SENDCTL_CID, pos) :: own) ly3 S3 W2 mem4 md (k + 0) ->
  sendctl_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp pos F ly3 S3 W2 mem4 md 0).
{ intros md HJ. split; [exact HJ|]. split; [rewrite EV0; lia|]. split; [exact FR3|].
  split; [rewrite <- Eab; exact Hperm4|]. split; [exact ELF|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo4)|].
  split; [exact KEPT|]. split; [exact SAV|]. split; [exact FLW | exact PKL]. }
(* the world relation at Bw: no byte of G is a byte of f *)
assert (TW2 : tw_at TMAP_B (aview segs (w_H W2) mem4) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) mem2)); [exact HTW|]. intros b n i Hbn Hi.
  assert (HG : inG TG.G_HARNESS_B (b + i))
    by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  apply Xgx; [exact HG|]. intros HE. cbv beta in HE.
  apply (FIMG (b + i)); [rewrite ZLOJ in HE; unfold SENDCTL_FOFF in HE; lia | exact (trans_g_img _ HG)]. }
(* the read-only bytes io_send's callees read: image bytes outside G *)
assert (ROM2 : trans_rom_view_rd W2 mem4).
{ intros a Ha. rewrite <- (HROM a Ha).
  destruct (trans_ro_rd_scoped B HROU HRNE a Ha) as [Hno Hne].
  apply (K3 a (trans_ro_img a Ha)); [|exact Hno | exact Hne].
  intros HG. pose proof (inG_G_HARNESS_hull a HG). pose proof (trans_ro_rd_bounds a Ha).
  unfold TG.G_HARNESS_B_LO in *. lia. }
(* the cells at kp and klp *)
assert (KVK : kp <> 0 -> forall a, kp <= a < kp + 60 -> aview segs (w_H W2) mem4 a = aview segs (w_H W) mem2 a).
{ intros Hkp a Ha. destruct HKP as [Hk0 | (_ & _ & TWK & _ & OWK & NGK & _)]; [exfalso; exact (Hkp Hk0)|].
  apply KAW; [|unfold decode_off_win in OWK; rewrite ESTK, FSTK in *; lia].
  destruct (TWK a Ha) as [(Hw & _) | HG]; [exact Hw | exfalso; exact (NGK a Ha HG)]. }
assert (KVKL : kp <> 0 -> forall a, klp <= a < klp + 8 -> aview segs (w_H W2) mem4 a = aview segs (w_H W) mem2 a).
{ intros Hkp a Ha.
  destruct HKP as [Hk0 | (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TWKL & _ & OWKL & NGKL & _)];
    [exfalso; exact (Hkp Hk0)|].
  apply KAW; [|unfold decode_off_win in OWKL; rewrite ESTK, FSTK in *; lia].
  destruct (TWKL a Ha) as [(Hw & _) | HG]; [exact Hw | exfalso; exact (NGKL a Ha HG)]. }
assert (GKs : kp <> 0 -> garr8 segs (mrestrict (w_H W2) mem4) kp (TW.zs K) /\
  garr8 segs (mrestrict (w_H W2) mem4) klp (TW.zs KL)).
{ intros Hkp.
  destruct INC as [Hk0 | (GK & _ & GKL & _)]; [exfalso; exact (Hkp Hk0)|].
  destruct HKP as [Hk0 | (_ & _ & _ & _ & _ & _ & LK & _ & _ & _ & _ & _ & _ & _ & LKL & _)];
    [exfalso; exact (Hkp Hk0)|].
  split.
  - apply (sfb_garr8_kept (w_H W) (w_H W2) mem2 mem4 kp _); [|exact GK].
    intros j Hj. unfold TW.zs in Hj. rewrite length_map, LK in Hj.
    change (Z.of_nat (Z.to_nat SENDCTL_F)) with 60 in Hj. apply (KVK Hkp). lia.
  - apply (sfb_garr8_kept (w_H W) (w_H W2) mem2 mem4 klp _); [|exact GKL].
    intros j Hj. unfold TW.zs in Hj. rewrite length_map, LKL in Hj.
    change (Z.of_nat 8) with 8 in Hj. apply (KVKL Hkp). lia. }
(* +0x1b0: `mv s5, a0` *)
apply (sfb_srr_step W2 regs4 _ mem4 _ _ md4 _ (fun rom m => sfb_step_mv regs4 m rom)).
intros mat2.
pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ4)
  as HJ5.
set (md5 := with_vm_backing (m_vm_lazy md4) mat2 md4) in *. clearbody md5.
set (regs5 := YK11.regupd regs4 21 (YK11.getr regs4 10)).
(* the callee-saved registers the cuts read *)
assert (KR : forall r0 : Z, acallee_saved r0 -> r0 <> 1 -> r0 <> 21 ->
  YK11.getr regs5 (Z_to_bv 5 r0) = YK11.getr regs2 (Z_to_bv 5 r0)).
{ intros r0 Hr H1 H21. unfold acallee_saved in Hr.
  assert (Hr32 : 0 <= r0 < 32) by lia.
  unfold regs5. rewrite getr_other.
  2:{ intros E. apply (f_equal (@bv_unsigned 5)) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E.
      change (bv_modulus 5) with 32 in E. rewrite Z.mod_small in E by lia. apply H21. exact E. }
  rewrite (HP4 r0 ltac:(unfold acallee_saved; lia)).
  unfold regs3. rewrite getr_other; [reflexivity|].
  intros E. apply (f_equal (@bv_unsigned 5)) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 5) with 32 in E. rewrite Z.mod_small in E by lia. apply H1. exact E. }
assert (Q2 : YK11.getr regs5 2 = w64 sp1) by (rewrite <- R2; apply (KR 2); unfold acallee_saved; lia).
assert (Q3 : YK11.getr regs5 3 = YK11.getr regs 3) by (rewrite <- R3; apply (KR 3); unfold acallee_saved; lia).
assert (Q4 : YK11.getr regs5 4 = YK11.getr regs 4) by (rewrite <- R4; apply (KR 4); unfold acallee_saved; lia).
assert (Q8 : YK11.getr regs5 8 = w64 (spZ regs)) by (rewrite <- R8; apply (KR 8); unfold acallee_saved; lia).
assert (Q9 : YK11.getr regs5 9 = w64 sp1) by (rewrite <- R9; apply (KR 9); unfold acallee_saved; lia).
assert (Q18 : YK11.getr regs5 18 = w64 F) by (rewrite <- R18; apply (KR 18); unfold acallee_saved; lia).
assert (Q19 : YK11.getr regs5 19 = w64 SENDCTL_S) by (rewrite <- R19; apply (KR 19); unfold acallee_saved; lia).
assert (Q20 : YK11.getr regs5 20 = w64 klp) by (rewrite <- R20; apply (KR 20); unfold acallee_saved; lia).
assert (Q22 : YK11.getr regs5 22 = w64 kp) by (rewrite <- R22; apply (KR 22); unfold acallee_saved; lia).
assert (Q23 : YK11.getr regs5 23 = w64 (F + SENDCTL_FOFF)) by (rewrite <- R23; apply (KR 23); unfold acallee_saved; lia).
assert (Q24 : YK11.getr regs5 24 = w64 (SHADOW_OFF + F / 8))
  by (rewrite <- R24; apply (KR 24); unfold acallee_saved; lia).
assert (Q25 : YK11.getr regs5 25 = w64 F) by (rewrite <- R25; apply (KR 25); unfold acallee_saved; lia).
assert (Q26 : YK11.getr regs5 26 = w64 SHADOW_OFF) by (rewrite <- R26; apply (KR 26); unfold acallee_saved; lia).
assert (Q27 : YK11.getr regs5 27 = YK11.getr regs 27) by (rewrite <- R27; apply (KR 27); unfold acallee_saved; lia).
assert (Q10 : YK11.getr regs5 10 = w64 (sendctl_code Bw)) by (unfold regs5; rewrite getr_other by reg_neq_tac; exact X10).
assert (Q21 : YK11.getr regs5 21 = w64 (sendctl_code Bw)) by (unfold regs5; rewrite getr_same by reg_neq_tac; exact X10).
destruct (sendctl_model _ _ _ _ _ _ _ _ HM) as [(Ec & EBw & Er & Ef) | (Ec & Hmode & Ef & _ & _ & _ & _)].
- (* n = -1: +0x1b4 `bltz a0` taken, to the release cut *)
  rewrite Ec in Q10, Q21.
  apply (sfb_srr_step W2 regs5 _ mem4 _ _ md5 _
    (fun rom m => sfb_step_blt_tk regs5 m rom ltac:(rewrite Q10; vm_compute; reflexivity))).
  intros mat3.
  pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ5)
    as HJ6.
  apply (REL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw
    Bw' pos sp1 F ly3 S3 W2 mem4 _ 0 regs5 HFIX).
  + split; [exact (CURm _ HJ6)|]. rewrite EBw. split; [exact TW2|]. split; [exact Hgf|].
    rewrite Ef. destruct (Z.eq_dec kp 0) as [Hk0 | Hkp]; [left; exact Hk0|]. right. exact (GKs Hkp).
  + rewrite Er. exact (conj Q2 (conj Q3 (conj Q4 (conj Q8 (conj Q9 (conj Q18 (conj Q21 (conj Q24 (conj Q25 Q27))))))))).
- (* n = 60: `bltz a0` not taken *)
  rewrite Ec in Q10, Q21.
  assert (LF : length f = Z.to_nat SENDCTL_F) by (rewrite Ef; exact (sendctl_len_fr Bw cmd ack (tw_len _ _ _ HTW0))).
  assert (GF : garr8 segs (mrestrict (w_H W2) mem4) (F + SENDCTL_FOFF) (TW.zs f)).
  { rewrite Ef, <- (sendctl_build_out Bw cmd ack oj Hmode LOJ). exact Xout. }
  assert (RF : decode_rd_ok W2 mem4 (F + SENDCTL_FOFF) SENDCTL_F).
  { apply (sfb_rd_ok_fake LAWS lyc S2 W W2 mem2 mem4 md2 (F + SENDCTL_FOFF) SENDCTL_F HAR2).
    - exists SENDCTL_CID, pos. split; [exact Hin2|]. rewrite <- EF, EFB. unfold SENDCTL_FOFF, SENDCTL_F. lia.
    - exact Roj.
    - unfold SENDCTL_F. lia.
    - intros a Ha. apply (sfb_garr8_vis _ _ _ _ a GF). unfold TW.zs. rewrite length_map, LF. exact Ha.
    - exact KSH. }
  apply (sfb_srr_step W2 regs5 _ mem4 _ _ md5 _
    (fun rom m => sfb_step_blt_ft regs5 m rom ltac:(rewrite Q10; vm_compute; reflexivity))).
  intros mat3.
  pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ5)
    as HJ6.
  set (md6 := with_vm_backing (m_vm_lazy md5) mat3 md5) in *. clearbody md6.
  assert (RS : sendctl_regs_send regs regs5 sp1 F SENDCTL_F)
    by exact (conj (conj Q2 (conj Q3 (conj Q4 (conj Q8 (conj Q9 (conj Q18 (conj Q21 (conj Q24 (conj Q25 Q27)))))))))
      (conj Q19 (conj Q23 Q26))).
  destruct (Z.eq_dec kp 0) as [Hk0 | Hkp].
  + (* kp = 0: +0x1b8 `beqz s6` taken, to the send cut *)
    apply (sfb_srr_step W2 regs5 _ mem4 _ _ md6 _
      (fun rom m => sfb_step_beq_tk regs5 m rom ltac:(rewrite Q22, Hk0; vm_compute; reflexivity))).
    intros mat4.
    pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat4 HJ6)
      as HJ7.
    apply (SEND LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw
      Bw' pos sp1 F ly3 S3 W2 mem4 _ 0 regs5 HFIX); [|exact RS].
    split; [exact (CURm _ HJ7)|]. split; [exact TW2|]. split; [exact ROM2|]. split; [exact LF|].
    split; [exact GF|]. split; [exact RF|]. left. exact Hk0.
  + (* kp <> 0: `beqz s6` not taken, to the keep cut *)
    assert (Hkp1 : 0 < kp /\ kp + 60 <= 2 ^ 63).
    { destruct HKP as [Hk0 | (Hkp0 & _ & _ & RDK & _)]; [exfalso; exact (Hkp Hk0)|].
      destruct RDK as (_ & _ & _ & _ & _ & H63). unfold SENDCTL_F in H63. lia. }
    apply (sfb_srr_step W2 regs5 _ mem4 _ _ md6 _
      (fun rom m => sfb_step_beq_ft regs5 m rom ltac:(rewrite Q22; unfold bv_eqb, w64;
         rewrite !unsigned_lit_small by lia; apply Z.eqb_neq; lia))).
    intros mat4.
    pose proof (ajournal_gx_materialize segs B LAWS transportb_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat4 HJ6)
      as HJ7.
    apply (KEEP LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw
      Bw' pos sp1 F ly3 S3 W2 mem4 _ 0 regs5 HFIX); [| exact (conj RS (conj Q20 Q22)) | exact Hkp].
    split; [exact (CURm _ HJ7)|]. split; [exact TW2|]. split; [exact ROM2|]. split; [exact LF|].
    split; [exact GF|]. split; [exact RF|].
    right.
    destruct (GKs Hkp) as (GK2 & GKL2).
    destruct INC as [Hk0 | (_ & RDKm & _ & RDKLm)]; [exfalso; exact (Hkp Hk0)|].
    destruct HKP as [Hk0 | (_ & FKP & _ & _ & _ & _ & _ & _ & _ & KL8 & TWKL & _ & _ & NGKL & _)];
      [exfalso; exact (Hkp Hk0)|].
    split; [exact GK2|]. split.
    { (* kp: a range of one of the caller's frames *)
      apply (decode_rd_ok_fake_kept B LAWS lyc S2 W W2 mem2 mem4 md2 kp SENDCTL_F HAR2).
      - destruct FKP as (c0 & p0 & Hc0 & H1 & H2). exists c0, p0. split; [rewrite Hfrs; right; exact Hc0 | lia].
      - exact RDKm.
      - unfold SENDCTL_F. lia.
      - intros a Ha. apply (KVK Hkp). unfold SENDCTL_F in Ha. lia.
      - exact KSH. }
    split; [exact GKL2|].
    { (* klp: in the caller's stack window, in a heap block, or in one of its own frames *)
      destruct RDKLm as (V1 & V2 & V3 & V4 & V5 & V6).
      split; [intros a Ha; rewrite (KVKL Hkp a Ha); exact (V1 a Ha)|].
      split; [|split; [|exact (conj V4 (conj V5 V6))]].
      - intros x Hx.
        destruct (TWKL x Hx) as [(Hw & _) | HG]; [|exfalso; exact (NGKL x Hx HG)].
        destruct Hw as [Hw | [(_ & b & m & Hb & Hr) | [(b & m & Hb & _ & Hr) | (c0 & p0 & Hc & Hr)]]].
        + destruct (can_stack_addressable segs B ly3 S3 W2 mem4 md4 x 1 HAR4 ltac:(rewrite ESL4; lia) ltac:(lia)
            ltac:(rewrite ESH4; lia) x ltac:(lia)) as (s & Hs1 & Hs2).
          exists s. exact (conj Hs1 Hs2).
        + destruct (range_addressable_of_block segs B LAWS ly3 S3 W2 mem4 md4 b m x 1 HAR4 (BL3 _ Hb)
            ltac:(lia) ltac:(lia) x ltac:(lia)) as (s & Hs1 & Hs2).
          exists s. exact (conj Hs1 Hs2).
        + destruct (range_addressable_of_block segs B LAWS ly3 S3 W2 mem4 md4 b m x 1 HAR4 (BL3 _ Hb)
            ltac:(lia) ltac:(lia) x ltac:(lia)) as (s & Hs1 & Hs2).
          exists s. exact (conj Hs1 Hs2).
        + assert (Hc' : In (c0, p0) (frames Sc)) by (rewrite HfrsC; apply in_or_app; left; exact Hc).
          destruct (TransportGCg.dkg_frame_al64 segs B _ _ _ _ _ c0 p0 HARc Hc') as (A1 & A2 & A3).
          destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c0 p0 HARc Hc') as (B1 & B2 & _).
          destruct (V2 x Hx) as (s & Hs1 & Hs2). exists s. split; [|exact Hs2].
          rewrite <- Hs1. apply (KSH c0 p0); [rewrite Hfrs; right; exact Hc'|].
          unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
          unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in V4.
          destruct Hr as [Hr | Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
          * pose proof (Z.div_mod (frame_addr lyc c0 p0) 64 ltac:(lia)).
            pose proof (Z.div_mod (fs_frame_bytes c0) 64 ltac:(lia)).
            pose proof (Z.div_mod (frame_addr lyc c0 p0) 8 ltac:(lia)).
            pose proof (Z.mod_pos_bound (frame_addr lyc c0 p0) 8 ltac:(lia)).
            pose proof (Z.div_mod (fs_frame_bytes c0) 8 ltac:(lia)).
            pose proof (Z.mod_pos_bound (fs_frame_bytes c0) 8 ltac:(lia)).
            pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
          * exfalso. unfold shadow_addr, SHADOW_OFF in Hr.
            pose proof (Z.div_pos (frame_addr lyc c0 p0) 8 ltac:(lia) ltac:(lia)).
            pose proof (shadow_range_end (frame_addr lyc c0 p0) (fs_frame_bytes c0) ltac:(lia)) as Hse.
            assert ((frame_addr lyc c0 p0 + fs_frame_bytes c0) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
            unfold shadow_addr, SHADOW_OFF in Hse. change (2 ^ 47 / 8) with (2 ^ 44) in *. lia.
      - apply sfb_hull_18; [exact KL8|]. intros s Hs.
        destruct (TWKL klp ltac:(lia)) as [(Hw & _) | HG]; [|exfalso; exact (NGKL klp ltac:(lia) HG)].
        destruct Hw as [Hw | [(_ & b & m & Hb & Hr) | [(b & m & Hb & _ & Hr) | (c0 & p0 & Hc & Hr)]]].
        + exact (can_stack_hull segs B ly3 S3 W2 mem4 md4 klp 1 HAR4 ltac:(rewrite ESL4; lia) ltac:(lia)
            ltac:(rewrite ESH4; lia) s Hs).
        + exact (shadow_hull_vis_of_block segs B LAWS ly3 S3 W2 mem4 md4 b m klp 1 HAR4 (BL3 _ Hb)
            ltac:(lia) ltac:(lia) ltac:(lia) s Hs).
        + exact (shadow_hull_vis_of_block segs B LAWS ly3 S3 W2 mem4 md4 b m klp 1 HAR4 (BL3 _ Hb)
            ltac:(lia) ltac:(lia) ltac:(lia) s Hs).
        + assert (Hc' : In (c0, p0) (frames Sc)) by (rewrite HfrsC; apply in_or_app; left; exact Hc).
          destruct (TransportGCg.dkg_frame_al64 segs B _ _ _ _ _ c0 p0 HARc Hc') as (A1 & A2 & A3).
          destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c0 p0 HARc Hc') as (B1 & B2 & _).
          unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in V4.
          destruct Hr as [Hr | Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
          * assert (Hhi : (frame_addr lyc c0 p0 + fs_frame_bytes c0) mod 64 = 0)
              by (rewrite Z.add_mod, A1, A2 by lia; reflexivity).
            destruct (YG0s.hull_inside (frame_addr lyc c0 p0) (frame_addr lyc c0 p0 + fs_frame_bytes c0) klp 1 s
              A1 Hhi ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hs) as (g & Hg8 & Hgr & Hsg).
            rewrite (KSH c0 p0 s); [apply V3; exact (sfb_hull_81_inv klp s KL8 Hs) | rewrite Hfrs; right; exact Hc'|].
            rewrite Hsg. unfold in_zr, shadow_addr. cbn [fst snd].
            pose proof (Z.div_mod (frame_addr lyc c0 p0) 64 ltac:(lia)).
            pose proof (Z.div_mod (fs_frame_bytes c0) 64 ltac:(lia)).
            pose proof (Z.div_mod (frame_addr lyc c0 p0) 8 ltac:(lia)).
            pose proof (Z.mod_pos_bound (frame_addr lyc c0 p0) 8 ltac:(lia)).
            pose proof (Z.div_mod (fs_frame_bytes c0) 8 ltac:(lia)).
            pose proof (Z.mod_pos_bound (fs_frame_bytes c0) 8 ltac:(lia)).
            pose proof (Z.div_mod g 8 ltac:(lia)). pose proof (Z.mod_pos_bound g 8 ltac:(lia)). lia.
          * exfalso. unfold shadow_addr, SHADOW_OFF in Hr.
            pose proof (Z.div_pos (frame_addr lyc c0 p0) 8 ltac:(lia) ltac:(lia)).
            pose proof (shadow_range_end (frame_addr lyc c0 p0) (fs_frame_bytes c0) ltac:(lia)) as Hse.
            assert ((frame_addr lyc c0 p0 + fs_frame_bytes c0) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
            unfold shadow_addr, SHADOW_OFF in Hse. change (2 ^ 47 / 8) with (2 ^ 44) in *. lia. }
Qed.

End fb.

Print Assumptions sendctl_fb.
