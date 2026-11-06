(* host_offset_cgW: Theorem transport_host_offset_cg_holds, the statement transport_host_offset_cg_holds_stmt of
   lib/B/Prog/host_offset_cg.v: the caller-journal walk of host_offset on fuzz_transport.asan-ubsan at 0x85040
   (192 bytes, frame 80, ten rounds, one call of the bcmp wrapper per round).

   The walk, from the contract's premises (ho_holds):
     1. an INNER journal at the entry state (ho_inner, YCbq.v ajournal_sub_init; stack window
        [spZ regs - HOFF_STK, spZ regs), no footprint, no frame of its own);
     2. the premises read once at the entry memory: trans_src_ok through the kit's trans_src_ok_rd
        (lib/B/Prog/DgnTransportBCg.v; ho_rdb, the only use of trans_src_ok), the body's bytes from garr8
        (ho_view_body), HOST's bytes from trans_rom_view_rd and the image (ho_view_host), and the model's rounds
        from host_offset_m Bw body = Some (Bw', r) (ho_model, ho_loop_step);
     3. the footprint runs of lib/B/Prog/host_offset_seg_run.v carried into SRr by lib/B/Prog/TransportFevt.v
        decode_run: ho_pro_F (the entry to the first call) and ho_tail_run_F (a call's return to the next call or
        to the `ret`); the inner journal is kept across the prologue by CgBNoTwin.v cgb_j_frame (it writes only its
        80-byte frame) and across a tail run by cgb_j_sbm (it writes nothing);
     4. each round's call is cut by YCbq.v aj_bcmp_at at the statement's abcmp_realizes premise (ho_bcmp) with
        (p + i, HOST, 6); the ranges are read ranges at the call state (ho_rd_vk for the body, ho_host_rd from
        trans_rom_view_rd and the record's shadow cells transport_cells / trans_hoff_cells), and the answer is 0
        exactly when the model's beq_bytes (sub body i 6) HOST is true (ho_cmp);
     5. the rounds are an induction on the model's fuel (ho_round): a hit returns i, a miss goes to round i + 1,
        and the tenth miss returns -1 (the model's host_offset_loop 0 = Some (-1));
     6. the inner journal and the caller's compose by YC85.v ajournal_sub_tok, the kept bytes are YCbq.v
        acall_kept_of_journal of the inner journal, the meter is unchanged (YC5d.v mle_start), the frames and
        blocks are the call state's, and Bw' = Bw is the model's (ho_close).
   The statement's trans_ro_rd_unowned and trans_rom_no_errno are not used: HOST's bytes are read from the entry
   state's trans_rom_view_rd and carried through the walk's own runs and calls. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
  YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI16 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CgBNoTwin YC85.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import host_offset_cg host_offset_seg_run.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module FCl := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TWd := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TCb := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.

(* ======== the model (lib/TModel/TCb.v host_offset_m), no machine ======== *)

(* host_offset_m returns the world it was given and the loop's answer. The world is not taken apart: the two
   projections are read off the equation (never `injection` on a world-carrying option). *)
Lemma ho_model : forall (Bw body Bw' : list byte) (r : Z),
  TCb.host_offset_m Bw body = Some (Bw', r) ->
  Bw' = Bw /\ TCb.host_offset_loop 10 body 0 = Some r.
Proof.
  intros Bw body Bw' r H. unfold TCb.host_offset_m in H. revert H.
  destruct (TCb.host_offset_loop 10 body 0) as [r0|] eqn:E; intros H; [|discriminate H].
  pose proof (f_equal (fun o : option (list byte * Z) => match o with Some (b, _) => b | None => Bw end) H) as HB.
  pose proof (f_equal (fun o : option (list byte * Z) => match o with Some (_, z) => z | None => 0 end) H) as HR.
  cbv beta iota in HB, HR.
  split; [symmetry; exact HB | rewrite ?E, HR; reflexivity].
Qed.

(* One round of the model: the window [i, i + 6) lies in the body, and the round either answers i or goes on. *)
Lemma ho_loop_step : forall (n : nat) (body : list byte) (i r : Z),
  0 <= i <= 9 -> TCb.host_offset_loop (Datatypes.S n) body i = Some r ->
  i + 6 <= Z.of_nat (length body) /\
  ((TCb.beq_bytes (TWd.sub body i 6) TCb.HOST = true /\ r = i) \/
   (TCb.beq_bytes (TWd.sub body i 6) TCb.HOST = false /\ TCb.host_offset_loop n body (i + 1) = Some r)).
Proof.
  intros n body i r Hi H. cbn [TCb.host_offset_loop] in H.
  replace (i + DgnSpec.SPEC_MAC <=? TCb.SPEC_ANN_UNKNOWN) with true in H
    by (symmetry; apply Z.leb_le; unfold DgnSpec.SPEC_MAC, TCb.SPEC_ANN_UNKNOWN; lia).
  cbv iota in H. revert H.
  destruct (Z.ltb_spec (Z.of_nat (length body)) (i + DgnSpec.SPEC_MAC)) as [HL|HL]; intros H;
    cbv iota in H.
  - discriminate H.
  - split; [unfold DgnSpec.SPEC_MAC in HL; lia|].
    revert H. destruct (TCb.beq_bytes (TWd.sub body i 6) TCb.HOST) eqn:EB; intros H; cbv iota in H.
    + left. split; [reflexivity|]. injection H as H. lia.
    + right. split; [reflexivity | exact H].
Qed.

Lemma ho_loop_zero : forall (body : list byte) (i r : Z), TCb.host_offset_loop 0 body i = Some r -> r = -1.
Proof. intros body i r H. cbn [TCb.host_offset_loop] in H. injection H as H. lia. Qed.

(* ---- the byte list the round compares ---- *)

Lemma ho_nth_firstn : forall (l : list byte) k j d, (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l j d H; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct j as [|j]; cbn; [reflexivity | apply IH; lia].
Qed.

Lemma ho_nth_skipn : forall (l : list byte) k j d, nth j (skipn k l) d = nth (k + j) l d.
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l j d; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct j; reflexivity | apply IH].
Qed.

Lemma ho_len_sub : forall (l : list byte) i, 0 <= i -> i + 6 <= Z.of_nat (length l) ->
  length (TWd.sub l i 6) = 6%nat.
Proof. intros l i H1 H2. unfold TWd.sub. rewrite length_firstn, length_skipn. lia. Qed.

Lemma ho_nth_sub : forall (l : list byte) i j d, 0 <= i -> 0 <= j < 6 ->
  nth (Z.to_nat j) (TWd.sub l i 6) d = nth (Z.to_nat (i + j)) l d.
Proof.
  intros l i j d Hi Hj. unfold TWd.sub.
  rewrite ho_nth_firstn by lia. rewrite ho_nth_skipn. f_equal. lia.
Qed.

Lemma ho_beq_spec : forall a b, TCb.beq_bytes a b = true <-> TWd.zs a = TWd.zs b.
Proof.
  intros a b. unfold TCb.beq_bytes.
  destruct (list_eq_dec Z.eq_dec (TWd.zs a) (TWd.zs b)) as [E|E]; split; intros H;
    [exact E | reflexivity | discriminate H | contradiction].
Qed.

(* Two six-byte lists read through two readers agree exactly when their values agree. *)
Lemma ho_cmp_iff : forall (l1 l2 : list byte) (f g : Z -> option Z),
  length l1 = 6%nat -> length l2 = 6%nat ->
  (forall i, 0 <= i < 6 -> f i = Some (bv_unsigned (nth (Z.to_nat i) l1 (Z_to_bv 8 0)))) ->
  (forall i, 0 <= i < 6 -> g i = Some (bv_unsigned (nth (Z.to_nat i) l2 (Z_to_bv 8 0)))) ->
  ((forall i, 0 <= i < 6 -> f i = g i) <-> TWd.zs l1 = TWd.zs l2).
Proof.
  intros l1 l2 f g L1 L2 HF HG. unfold TWd.zs. split.
  - intros E. apply nth_ext with (d := bv_unsigned (Z_to_bv 8 0)) (d' := bv_unsigned (Z_to_bv 8 0));
      [rewrite !length_map; lia|].
    intros j Hj. rewrite length_map in Hj. rewrite !map_nth.
    pose proof (E (Z.of_nat j) ltac:(lia)) as Ej.
    rewrite (HF (Z.of_nat j) ltac:(lia)), (HG (Z.of_nat j) ltac:(lia)) in Ej.
    rewrite Nat2Z.id in Ej. injection Ej as Ej. exact Ej.
  - intros E i Hi. rewrite (HF i Hi), (HG i Hi). f_equal.
    pose proof (f_equal (fun l => nth (Z.to_nat i) l (bv_unsigned (Z_to_bv 8 0))) E) as Ei.
    cbv beta in Ei. rewrite !map_nth in Ei. exact Ei.
Qed.

(* garr8's bytes, as byte values. *)
Lemma ho_nth_map_bz : forall (l : list byte) i, (i < length l)%nat ->
  nth i (map DgnSpec.bz l) 0 = DgnSpec.bz (nth i l (Z_to_bv 8 0)).
Proof.
  induction l as [|b l IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [map nth length] in *. apply IH. lia.
Qed.

Lemma ho_b8_bz : forall b : byte, Z_to_bv 8 (le_byte (DgnSpec.bz b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hbr. unfold bv_modulus in Hbr.
  change (2 ^ Z.of_N 8) with 256 in Hbr. unfold le_byte, DgnSpec.bz.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
  rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* ---- HOST, the image's six bytes at 0x20fe0 ---- *)

Lemma ho_in_ro : forall j, 0 <= j < 6 -> trans_in_ro_rd (HO_HOST + j).
Proof.
  intros j Hj. unfold trans_in_ro_rd, TRANS_RO_RD, TRANS_RO_GLOBALS. apply Exists_exists.
  exists (TRANS_HOST, 6). split; [cbn; tauto|]. unfold in_zr, TRANS_HOST, HO_HOST. cbn [fst snd]. lia.
Qed.

Lemma ho_host_rom : forall j, 0 <= j < 6 ->
  option_map (fun b : byte => bv_unsigned b) (YKK.seg_rom tfibsegs (Z_to_bv 64 (HO_HOST + j)))
  = Some (bv_unsigned (nth (Z.to_nat j) TCb.HOST (Z_to_bv 8 0))).
Proof.
  intros j Hj. assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

(* A one-byte constant cell of the record, read at an AR state. *)
Lemma ho_const1 : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s = Some v.
Proof.
  intros rc B ly S W mem md a v s HAR Hin Hv <-.
  pose proof (am_const _ _ _ _ (proj1 HAR)) as HC.
  pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc. unfold z1, c1, cell_holds in Hc.
  cbn [c_at c_w c_val aeval] in Hc. specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
  change (aeval B ly (ANum v)) with v in Hc.
  rewrite Hc. f_equal. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma ho_const1_nn : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s <> None.
Proof.
  intros rc B ly S W mem md a v s H1 H2 H3 H4.
  rewrite (ho_const1 B ly S W mem md a v s H1 H2 H3 H4). discriminate.
Qed.

(* Present bytes make a writable stack range. *)
Lemma ho_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* ======== the walk ======== *)

Section Walk.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation ajournalB := (@ajournal rc YE2k.tfib_sink_head tfibsegs B).

Hypothesis HCELLS : transport_cells B.
Hypothesis HHOFF : trans_hoff_cells B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMPH : forall fx' : YKK.FPState,
  @abcmp_realizes fx' rc tfibsegs B (transportb_sigma TB___interceptor_trampoline_bcmp).

Section Call.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (p r : Z) (body Bw Bw' : list byte).

Hypothesis HJ : ajournalB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HRET : YK0s.ret_ok (YKK.getr regs 1).
Hypothesis HRA4 : 4096 <= raZ regs.
Hypothesis HGP : YKK.getr regs 3 = w64 (as_gp B).
Hypothesis HTP : YKK.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YKK.getr regs 10 = w64 p.
Hypothesis HAL : spZ regs mod 16 = 0.
Hypothesis HWLO : sp0 - STK <= spZ regs - HOFF_STK.
Hypothesis HWHI : spZ regs <= sp0.
Hypothesis HP0 : 0 < p.
Hypothesis GBB : garr8 tfibsegs (mrestrict (w_H W) memc) p (map DgnSpec.bz body).
Hypothesis HSRC : trans_src_ok B lyc Sc W memc p (Z.of_nat (length body)).
Hypothesis OWB : decode_off_win regs HOFF_STK p (Z.of_nat (length body)).
Hypothesis HROM : trans_rom_view_rd W memc.
Hypothesis HMOD : TCb.host_offset_m Bw body = Some (Bw', r).
Hypothesis HNEV : st_nev S + k + HOFF_EV <= EV_MAX.

Local Ltac ho_lia := unfold HOFF_STK, HOFF_FRAME, ESTACK, HO_HOST in *; lia.

(* ---- what the journal says about the entry state ---- *)

Lemma ho_AR : AR tfibsegs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma ho_stk_ok : astk_ok STK ly sp0.
Proof.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & _). exact HS.
Qed.

Lemma ho_pres : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a.
Proof.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _). exact HP.
Qed.

Lemma ho_sp_rng : YM05.alloc_ceiling + HOFF_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof. pose proof ho_stk_ok as (H16 & Hstk0 & Hceil & Hlo & Hhi & H47 & _). lia. Qed.

(* ---- the model at this call ---- *)

Lemma ho_mod : Bw' = Bw /\ TCb.host_offset_loop 10 body 0 = Some r.
Proof. exact (ho_model Bw body Bw' r HMOD). Qed.

Lemma ho_len : 6 <= Z.of_nat (length body).
Proof.
  pose proof ho_mod as (_ & HL).
  destruct (ho_loop_step 9 body 0 r ltac:(lia) HL) as (H6 & _). lia.
Qed.

(* the body's facts, through the kit's trans_src_ok_rd *)
Lemma ho_rdb : decode_rd_ok W memc p (Z.of_nat (length body)).
Proof.
  exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc p _ ho_AR HSRC ltac:(pose proof ho_len; lia)).
Qed.

(* the body's bytes, as the entry view reads them *)
Lemma ho_view_body : forall i, 0 <= i < Z.of_nat (length body) ->
  aview tfibsegs (w_H W) memc (p + i) = Some (bv_unsigned (nth (Z.to_nat i) body (Z_to_bv 8 0))).
Proof.
  intros i Hi. destruct (GBB (Z.to_nat i) ltac:(rewrite length_map; lia)) as [HV1 _].
  specialize (HV1 0%nat ltac:(lia)). cbn [Z.of_nat] in HV1. rewrite Z.add_0_r, Z2Nat.id in HV1 by lia.
  unfold aview. cbv beta. rewrite HV1. cbn [option_map]. f_equal. f_equal.
  rewrite (ho_nth_map_bz body (Z.to_nat i) ltac:(lia)). apply ho_b8_bz.
Qed.

(* HOST's bytes, as the entry view reads them *)
Lemma ho_view_host : forall j, 0 <= j < 6 ->
  aview tfibsegs (w_H W) memc (HO_HOST + j) = Some (bv_unsigned (nth (Z.to_nat j) TCb.HOST (Z_to_bv 8 0))).
Proof. intros j Hj. rewrite (HROM _ (ho_in_ro j Hj)). exact (ho_host_rom j Hj). Qed.

(* ---- the memories of the walk: their view outside the call's stack window ---- *)

Definition ho_vk (mm : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - HOFF_STK \/ spZ regs <= a) ->
    aview tfibsegs (w_H W) mm a = aview tfibsegs (w_H W) memc a.

Lemma ho_vk_refl : ho_vk memc.
Proof. intros a _ _. reflexivity. Qed.

Lemma ho_vk_munch : forall mm, munch [(spZ regs + -80, spZ regs)] memc mm -> ho_vk mm.
Proof.
  intros mm MU a Ha Hd. apply aview_eq_of. unfold mrestrict.
  destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
  pose proof ho_sp_rng as [SP1 SP2].
  apply MU. cbn [outside]. rewrite unsigned_lit by lia. split; [ho_lia | exact I].
Qed.

Lemma ho_vk_call : forall m1 m2, ho_vk m1 ->
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - HOFF_STK \/ spZ regs + -80 <= a) ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a) -> ho_vk m2.
Proof.
  intros m1 m2 V1 E a H1 H2. rewrite (E a H1 ltac:(destruct H2; [left | right]; ho_lia)). exact (V1 a H1 H2).
Qed.

Lemma ho_rd_vk : forall mm q n, ho_vk mm -> decode_rd_ok W memc q n ->
  (q + n <= spZ regs - HOFF_STK \/ spZ regs <= q) -> decode_rd_ok W mm q n.
Proof.
  intros mm q n VK RD OFF.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof ho_sp_rng as [SP1 SP2].
  pose proof RD as (_ & _ & _ & Hm & H0 & H63).
  apply (trans_rd_ok_view W W memc mm q n RD).
  - intros a Ha. apply VK; [ho_lia | destruct OFF; [left | right]; ho_lia].
  - intros s' Hs. apply VK; [unfold kLowMemEnd, kHighShadowEnd in *; ho_lia |
                             left; unfold kHighShadowEnd in *; ho_lia].
Qed.

Lemma ho_view_vk : forall mm a, ho_vk mm -> 0 <= a < 2 ^ 64 ->
  (a + 1 <= spZ regs - HOFF_STK \/ spZ regs <= a) ->
  aview tfibsegs (w_H W) mm a = aview tfibsegs (w_H W) memc a.
Proof. intros mm a VK H1 H2. exact (VK a H1 H2). Qed.

(* HOST's read range at any state of the walk: its bytes (the record's read-only view), its payload's shadow byte
   (transport_cells: 6) and the eight shadow bytes of its hull [0x7fffc1f8, 0x7fffc200) (trans_hoff_cells: the
   redzone of LLVMFuzzerTestOneInput.SCALE and HOST's own guard granules). *)
Lemma ho_host_rd : forall mm ly' S' md', ho_vk mm -> @AR rc tfibsegs B ly' S' W mm md' ->
  decode_rd_ok W mm HO_HOST 6.
Proof.
  intros mm ly' S' md' VK HAR.
  pose proof ho_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (HCELLS ly') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH & _).
  destruct (HHOFF ly') as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. rewrite (VK a ltac:(ho_lia) ltac:(left; ho_lia)).
    replace a with (HO_HOST + (a - HO_HOST)) by lia.
    rewrite (HROM _ (ho_in_ro (a - HO_HOST) ltac:(unfold HO_HOST in *; lia))),
            (ho_host_rom (a - HO_HOST) ltac:(unfold HO_HOST in *; lia)).
    discriminate.
  - intros x Hx. exists 6. split.
    + eapply (ho_const1 B ly' S' W mm md'); [exact HAR | exact RH | lia |].
      unfold FCl.shadow_addr, FCl.ASAN_K, TRANS_HOST, shadow_of_addr, SHADOW_OFF, HO_HOST in *.
      Z.div_mod_to_equations. lia.
    + unfold saddr_ok, HO_HOST in *. right. Z.div_mod_to_equations. lia.
  - intros s' Hs. unfold shadow_addr, SHADOW_OFF, HO_HOST in Hs. cbn in Hs.
    assert (Hc : s' = 2147467768 \/ s' = 2147467769 \/ s' = 2147467770 \/ s' = 2147467771 \/
                 s' = 2147467772 \/ s' = 2147467773 \/ s' = 2147467774 \/ s' = 2147467775) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ eapply ho_const1_nn; [exact HAR | exact D1 | lia | reflexivity]
      | eapply ho_const1_nn; [exact HAR | exact D2 | lia | reflexivity]
      | eapply ho_const1_nn; [exact HAR | exact D3 | lia | reflexivity]
      | eapply ho_const1_nn; [exact HAR | exact D4 | lia | reflexivity]
      | eapply ho_const1_nn; [exact HAR | exact RH | lia | reflexivity]
      | eapply ho_const1_nn; [exact HAR | exact D5 | lia | reflexivity]
      | eapply ho_const1_nn; [exact HAR | exact D6 | lia | reflexivity]
      | eapply ho_const1_nn; [exact HAR | exact D7 | lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd, HO_HOST. lia.
  - unfold HO_HOST. lia.
  - unfold HO_HOST. lia.
Qed.

(* bcmp's test of [p + i, p + i + 6) against HOST, at a memory whose view of both is the entry state's: it is the
   model's beq_bytes (sub body i 6) HOST. *)
Lemma ho_cmp : forall (mT : word -> option byte) (i : Z), ho_vk mT ->
  0 <= i -> i + 6 <= Z.of_nat (length body) ->
  ((forall j, 0 <= j < 6 -> aview tfibsegs (w_H W) mT (p + i + j) = aview tfibsegs (w_H W) mT (HO_HOST + j)) <->
   TCb.beq_bytes (TWd.sub body i 6) TCb.HOST = true).
Proof.
  intros mT i VK Hi HL.
  pose proof ho_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof ho_rdb as (_ & _ & _ & _ & H0F & H63F).
  pose proof OWB as OF. unfold decode_off_win in OF.
  etransitivity; [|symmetry; apply ho_beq_spec].
  apply (ho_cmp_iff (TWd.sub body i 6) TCb.HOST
           (fun j => aview tfibsegs (w_H W) mT (p + i + j))
           (fun j => aview tfibsegs (w_H W) mT (HO_HOST + j))).
  - apply ho_len_sub; lia.
  - reflexivity.
  - intros j Hj. cbv beta.
    rewrite (VK (p + i + j) ltac:(lia) ltac:(destruct OF; [left | right]; ho_lia)).
    replace (p + i + j) with (p + (i + j)) by lia.
    rewrite (ho_view_body (i + j) ltac:(lia)).
    rewrite (ho_nth_sub body i j (Z_to_bv 8 0) ltac:(lia) Hj). reflexivity.
  - intros j Hj. cbv beta.
    rewrite (VK (HO_HOST + j) ltac:(ho_lia) ltac:(left; ho_lia)).
    exact (ho_view_host j Hj).
Qed.

(* ---- the inner journal ---- *)

Lemma ho_inner : ajournalB HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0.
Proof.
  pose proof ho_stk_ok as (Hal16 & _).
  apply (@ajournal_sub_init rc YE2k.tfib_sink_head tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
           HOFF_STK (spZ regs) [] (spZ regs - sp0) HJ);
    [lia | rewrite Zminus_mod, HAL, Hal16; reflexivity | lia | ho_lia | lia].
Qed.

(* The inner journal across the prologue, which writes only the 80 bytes of its frame. *)
Lemma ho_journal_pro : forall (mem1 : word -> option byte) (md1 : Model),
  munch [(spZ regs + -80, spZ regs)] memc mem1 -> YK1b.mem_grows memc mem1 ->
  same_but_materialized mdc md1 ->
  ajournalB HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem1 md1 0.
Proof.
  intros mem1 md1 MU GR SBM.
  apply (@cgb_j_frame rc B LAWS HOFF_STK 80 lyc Sc W memc mdc (spZ regs) lyc Sc W memc mdc 0 mem1 md1);
    [ho_lia | exact ho_inner | | exact GR | exact SBM].
  intros x Hx. apply MU. cbn [outside]. split; [lia | exact I].
Qed.

(* ---- the close ---- *)

Lemma ho_close : forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
  ajournalB HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
  aregs_preserved regs regs2 ->
  YKK.getr regs2 (Z_to_bv 5 10) = w64 r ->
  SRr tfibsegs W (mkCfg (@YKK.mkst fx regs2 (YKK.getr regs 1) mem2 (YKK.seg_rom tfibsegs)) md2)
    (transport_hoff_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).
Proof.
  intros regs2 mem2 md2 JI HP HA0.
  pose proof ho_mod as (EBw & _).
  apply SRr_ret. unfold transport_hoff_post, decode_cg_post.
  exists lyc, Sc, regs2, mem2, md2, 0.
  split; [reflexivity|].
  split; [unfold HOFF_EV; lia|].
  split.
  { pose proof (ajournal_sub_tok tfibsegs B LAWS decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  HOFF_STK (spZ regs) [] [] lyc Sc W mem2 md2 0 HJ JI HWLO HWHI
                  ltac:(intros a (rg & Hr & _); destruct Hr)) as J.
    cbn [app] in J. exact J. }
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { exact (acall_kept_of_journal tfibsegs B decode_segs_low HOFF_STK (spZ regs) [] [] lyc Sc W memc mdc
             lyc Sc W mem2 md2 0 (fun _ => False) JI ho_AR
             ltac:(intros a (rg & Hr & _); destruct Hr)
             ltac:(intros bq mq i Hb _ _; exact Hb)
             sink_closed_nil). }
  split; [exact (mle_start MT Sc MTL)|].
  split; [exact HA0 | exact EBw].
Qed.

(* The registers the epilogue restores are the caller's. *)
Lemma ho_pres_ret : forall (sw r10 x5 x6 x7 a1v a2v x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  bv_unsigned sw = spZ regs - 80 ->
  aregs_preserved regs
    (mkR (YKK.getr regs (Z_to_bv 5 1)) (Z_to_bv 64 (bv_unsigned sw + 80))
         (YKK.getr regs (Z_to_bv 5 3)) (YKK.getr regs (Z_to_bv 5 4)) x5 x6 x7
         (YKK.getr regs (Z_to_bv 5 8)) (YKK.getr regs (Z_to_bv 5 9)) r10 a1v a2v x13 x14 x15 x16 x17
         (YKK.getr regs (Z_to_bv 5 18)) (YKK.getr regs (Z_to_bv 5 19)) (YKK.getr regs (Z_to_bv 5 20))
         (YKK.getr regs (Z_to_bv 5 21)) (YKK.getr regs (Z_to_bv 5 22)) (YKK.getr regs (Z_to_bv 5 23))
         (YKK.getr regs (Z_to_bv 5 24)) (YKK.getr regs (Z_to_bv 5 25)) (YKK.getr regs (Z_to_bv 5 26))
         (YKK.getr regs (Z_to_bv 5 27)) x28 x29 x30 x31).
Proof.
  intros sw r10 x5 x6 x7 a1v a2v x13 x14 x15 x16 x17 x28 x29 x30 x31 Hsw rr Hr.
  unfold acallee_saved in Hr.
  assert (Hc : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst rr; try reflexivity.
  transitivity (Z_to_bv 64 (bv_unsigned sw + 80)); [reflexivity|].
  rewrite Hsw. replace (spZ regs - 80 + 80) with (spZ regs) by lia.
  unfold spZ. apply Z_to_bv_lit_self.
Qed.

(* The registers of a register map equivalent to a concrete map. *)
Lemma ho_pres_xeqv : forall (R R' : bvmap 5 word),
  Regs6ss.xregs_eqv R R' -> aregs_preserved regs R -> aregs_preserved regs R'.
Proof.
  intros R R' HX HP rr Hr. rewrite (decode_getr_xeqv R R' HX (Z_to_bv 5 rr)). exact (HP rr Hr).
Qed.

(* A writable stack range from the inner journal's present bytes. *)
Lemma ho_stk_of_journal : forall mem2 md2 hi,
  ajournalB HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
  spZ regs - HOFF_STK <= hi -> hi <= spZ regs ->
  stk rsegs mem2 (spZ regs - HOFF_STK) hi.
Proof.
  intros mem2 md2 hi JI H1 H2.
  pose proof ho_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & _).
  destruct JI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  apply (ho_stk_present (w_H W)); [ho_lia | ho_lia|]. intros a Ha. apply HP. ho_lia.
Qed.

(* The frame the prologue wrote is kept by a call whose window lies below it. *)
Lemma ho_frame_call : forall (mem1 mem2 : word -> option byte) (md1 : Model) (cs : list cell),
  ajournalB HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem1 md1 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - HOFF_STK \/ spZ regs + -80 <= a) ->
     aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem1 a) ->
  (forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem2 a) ->
  rw_cells rsegs mem1 (spZ regs + -80) cs -> Z.of_nat (cells_size cs) = 80 ->
  rw_cells rsegs mem2 (spZ regs + -80) cs.
Proof.
  intros mem1 mem2 md1 cs JI Hview Happ FR Hsz.
  pose proof ho_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & _).
  pose proof JI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  apply (decode_rw_cells_eq mem1 mem2 _ cs FR).
  rewrite Hsz. intros i Hi.
  assert (Hp1 : apresent (w_H W) mem1 (spZ regs + -80 + i)) by (apply HP; ho_lia).
  (* the byte of the frame is the one the call left *)
  apply (decode_byte_eq (w_H W) (w_H W) mem1 mem2 (spZ regs + -80 + i) Hp1 (Happ _ Hp1)).
  exact (Hview (spZ regs + -80 + i) ltac:(ho_lia) ltac:(right; lia)).
Qed.

(* ---- one call of bcmp on the inner journal (YCbq.v aj_bcmp_at at the statement's abcmp_realizes) ---- *)

Lemma ho_bcmp : forall (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model)
    (x y : Z) (raw : word) (Q : world tfibsegs -> config -> Prop),
  ajournalB HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memT mdT 0 ->
  YKK.getr regsT (Z_to_bv 5 10) = w64 x -> YKK.getr regsT (Z_to_bv 5 11) = w64 y ->
  YKK.getr regsT (Z_to_bv 5 12) = w64 6 ->
  decode_rd_ok W memT x 6 -> decode_rd_ok W memT y 6 ->
  (x + 6 <= spZ regs - HOFF_STK \/ spZ regs <= x) ->
  (y + 6 <= spZ regs - HOFF_STK \/ spZ regs <= y) ->
  YKK.getr regsT (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -80) ->
  YKK.getr regsT (Z_to_bv 5 3) = w64 (as_gp B) -> YKK.getr regsT (Z_to_bv 5 4) = w64 (as_tp B) ->
  YKK.getr regsT (Z_to_bv 5 1) = raw -> YK0s.ret_ok raw ->
  (forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) (v : word),
     ajournalB HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
     aregs_preserved regsT regs2 -> YKK.getr regs2 (Z_to_bv 5 10) = v ->
     (v = w64 0 <-> forall j, 0 <= j < 6 ->
        aview tfibsegs (w_H W) memT (x + j) = aview tfibsegs (w_H W) memT (y + j)) ->
     (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - HOFF_STK \/ spZ regs + -80 <= a) ->
        aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) ->
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
     SRr tfibsegs W (mkCfg (@YKK.mkst fx regs2 raw mem2 (YKK.seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W
    (mkCfg (@YKK.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) memT
              (YKK.seg_rom tfibsegs)) mdT) Q.
Proof.
  intros regsT memT mdT x y raw Q JI R10 R11 R12 RDX RDY OFX OFY R2 R3 R4 R1 HRAW K.
  pose proof ho_sp_rng as [SP1 SP2].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof RDX as (HvX & HraX & HhX & HmX & H0X & H63X).
  pose proof RDY as (HvY & HraY & HhY & HmY & H0Y & H63Y).
  assert (HspT : spZ regsT = spZ regs + -80).
  { change (spZ regsT) with (bv_unsigned (YKK.getr regsT (Z_to_bv 5 2))).
    rewrite R2, unsigned_lit by ho_lia. reflexivity. }
  eapply SRr_bind.
  { apply (@aj_bcmp_at fx rc YE2k.tfib_sink_head tfibsegs B LAWS decode_segs_low
             (transportb_sigma TB___interceptor_trampoline_bcmp) (ABCMPH fx) W regsT memT
             HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc mdT 0 x y 6 (-80) raw JI).
    - exact R10.
    - exact R11.
    - exact R12.
    - lia.
    - exact H0X.
    - lia.
    - exact H0Y.
    - lia.
    - exact HspT.
    - reflexivity.
    - lia.
    - ho_lia.
    - exact R3.
    - exact R4.
    - exact R1.
    - exact HRAW.
    - intros a Ha. split; [exact (HvX a Ha)|]. rewrite HspT. ho_lia.
    - intros a Ha. split; [exact (HvY a Ha)|]. rewrite HspT. ho_lia.
    - intros a Ha. ho_lia.
    - intros a Ha. ho_lia.
    - exact HmX.
    - exact HmY.
    - exact HraX.
    - intros _. exact HhX.
    - exact HraY.
    - intros _. exact HhY. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & JI2 & HP2 & Hv & Hiff & Hview & Happ).
  apply (K regs2 mem2 md2 v JI2 HP2 Hv Hiff).
  - intros a Ha1 Ha2. apply Hview; [lia|]. destruct Ha2; ho_lia.
  - exact Happ.
Qed.

(* ---- the rounds ---- *)

(* The register shape at the call of round i: the arguments, the loop's callee-saved registers, and the entry's
   gp, tp and s8 .. s11 (the walk's post needs them unchanged). *)
Definition ho_regs_at (regsT : bvmap 5 word) (i : Z) : Prop :=
  YKK.getr regsT (Z_to_bv 5 1) = Z_to_bv 64 HO_RET1 /\
  YKK.getr regsT (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -80) /\
  YKK.getr regsT (Z_to_bv 5 3) = YKK.getr regs (Z_to_bv 5 3) /\
  YKK.getr regsT (Z_to_bv 5 4) = YKK.getr regs (Z_to_bv 5 4) /\
  YKK.getr regsT (Z_to_bv 5 8) = Z_to_bv 64 i /\
  YKK.getr regsT (Z_to_bv 5 9) = Z_to_bv 64 p /\
  YKK.getr regsT (Z_to_bv 5 10) = Z_to_bv 64 (p + i) /\
  YKK.getr regsT (Z_to_bv 5 11) = Z_to_bv 64 HO_HOST /\
  YKK.getr regsT (Z_to_bv 5 12) = Z_to_bv 64 6 /\
  YKK.getr regsT (Z_to_bv 5 18) = Z_to_bv 64 HO_HOST /\
  YKK.getr regsT (Z_to_bv 5 19) = Z_to_bv 64 (p + i) /\
  YKK.getr regsT (Z_to_bv 5 20) = Z_to_bv 64 (0 - p) /\
  YKK.getr regsT (Z_to_bv 5 21) = Z_to_bv 64 (10 - i) /\
  YKK.getr regsT (Z_to_bv 5 22) = Z_to_bv 64 1 /\
  YKK.getr regsT (Z_to_bv 5 23) = Z_to_bv 64 (p + i) /\
  YKK.getr regsT (Z_to_bv 5 24) = YKK.getr regs (Z_to_bv 5 24) /\
  YKK.getr regsT (Z_to_bv 5 25) = YKK.getr regs (Z_to_bv 5 25) /\
  YKK.getr regsT (Z_to_bv 5 26) = YKK.getr regs (Z_to_bv 5 26) /\
  YKK.getr regsT (Z_to_bv 5 27) = YKK.getr regs (Z_to_bv 5 27).

(* The frame as the prologue wrote it: the entry's s7 .. s0 and ra. *)
Definition ho_frame (junk : list byte) : list cell :=
  ho_fr junk (YKK.getr regs (Z_to_bv 5 23)) (YKK.getr regs (Z_to_bv 5 22)) (YKK.getr regs (Z_to_bv 5 21))
        (YKK.getr regs (Z_to_bv 5 20)) (YKK.getr regs (Z_to_bv 5 19)) (YKK.getr regs (Z_to_bv 5 18))
        (YKK.getr regs (Z_to_bv 5 9)) (YKK.getr regs (Z_to_bv 5 8)) (YKK.getr regs (Z_to_bv 5 1)).

Lemma ho_frame_size : forall junk, length junk = 8%nat -> Z.of_nat (cells_size (ho_frame junk)) = 80.
Proof. intros junk HL. unfold ho_frame, ho_fr. cbn [cells_size csize]. lia. Qed.

Lemma ho_round : forall (n : nat) (i : Z) (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model)
    (junk : list byte),
  Z.of_nat n = 10 - i -> 0 <= i <= 9 ->
  TCb.host_offset_loop n body i = Some r ->
  ajournalB HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memT mdT 0 ->
  ho_vk memT ->
  rw_cells rsegs memT (spZ regs + -80) (ho_frame junk) ->
  length junk = 8%nat ->
  ho_regs_at regsT i ->
  SRr tfibsegs W (mkCfg (@YKK.mkst fx regsT (Z_to_bv 64 HO_BCMP) memT (YKK.seg_rom tfibsegs)) mdT)
    (transport_hoff_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).
Proof.
  pose proof ho_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof ho_rdb as RDB. pose proof RDB as (_ & _ & _ & RBm & RB0 & RB63).
  pose proof OWB as OF. unfold decode_off_win in OF.
  assert (GRET : ret_pc (YKK.getr regs (Z_to_bv 5 1)) = YKK.getr regs (Z_to_bv 5 1))
    by exact (LeafCgFacts.ret_ok_stmt_YK0s _ HRET).
  intros n. induction n as [|n IH]; intros i regsT memT mdT junk Hn Hi HL JI VK FR LJ RG.
  - lia.
  - destruct (ho_loop_step n body i r Hi HL) as (HLEN & HCASE).
    destruct RG as (T1 & T2 & T3 & T4 & T8 & T9 & T10 & T11 & T12 & T18 & T19 & T20 & T21 & T22 & T23
                    & T24 & T25 & T26 & T27).
    (* the read ranges of this round's call *)
    assert (RDX : decode_rd_ok W memT (p + i) 6).
    { apply (ho_rd_vk memT (p + i) 6 VK);
        [exact (trans_rd_ok_sub W memc p _ (p + i) 6 RDB ltac:(lia) ltac:(lia) ltac:(lia))
        | destruct OF; [left | right]; ho_lia]. }
    assert (RDY : decode_rd_ok W memT HO_HOST 6) by exact (ho_host_rd memT lyc Sc mdT VK (proj1 JI)).
    (* the call *)
    eapply (ho_bcmp regsT memT mdT (p + i) HO_HOST (Z_to_bv 64 HO_RET1));
      [ exact JI | exact T10 | exact T11 | exact T12 | exact RDX | exact RDY
      | destruct OF; [left | right]; ho_lia | left; ho_lia
      | exact T2 | rewrite T3; exact HGP | rewrite T4; exact HTP | exact T1
      | apply YK0s.ret_ok_even; vm_compute; reflexivity | ].
    intros regs2 mem2 md2 v JI2 HP2 Hv Hiff Hview Happ.
    assert (VK2 : ho_vk mem2) by exact (ho_vk_call memT mem2 VK Hview).
    pose proof (ho_frame_call memT mem2 mdT _ JI Hview Happ FR (ho_frame_size junk LJ)) as FR2.
    assert (CMP : v = w64 0 <-> TCb.beq_bytes (TWd.sub body i 6) TCb.HOST = true).
    { etransitivity; [exact Hiff|]. exact (ho_cmp memT i VK ltac:(lia) HLEN). }
    pose proof JI2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES2 & _).
    assert (RNG2 : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) (spZ regs + -80) 80).
    { apply (decode_rng_vis W); [ho_lia | ho_lia|]. intros j Hj.
      exact (proj1 (HPRES2 (spZ regs + -80 + j) ltac:(ho_lia))). }
    (* the run from the call's return *)
    eapply decode_run.
    { unfold LCK.ms_of_regs.
      rewrite (HP2 2 ltac:(unfold acallee_saved; lia)), (HP2 3 ltac:(unfold acallee_saved; lia)),
        (HP2 4 ltac:(unfold acallee_saved; lia)), (HP2 8 ltac:(unfold acallee_saved; lia)),
        (HP2 9 ltac:(unfold acallee_saved; lia)), (HP2 18 ltac:(unfold acallee_saved; lia)),
        (HP2 19 ltac:(unfold acallee_saved; lia)), (HP2 20 ltac:(unfold acallee_saved; lia)),
        (HP2 21 ltac:(unfold acallee_saved; lia)), (HP2 22 ltac:(unfold acallee_saved; lia)),
        (HP2 23 ltac:(unfold acallee_saved; lia)), (HP2 24 ltac:(unfold acallee_saved; lia)),
        (HP2 25 ltac:(unfold acallee_saved; lia)), (HP2 26 ltac:(unfold acallee_saved; lia)),
        (HP2 27 ltac:(unfold acallee_saved; lia)).
      rewrite T2, T3, T4, T8, T9, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, Hv.
      unfold ho_frame in FR2.
      apply ho_tail_run_F with (p := p) (i := i) (q := p + i) (f := 10 - i) (junk := junk)
        (c7 := YKK.getr regs (Z_to_bv 5 23)) (c6 := YKK.getr regs (Z_to_bv 5 22))
        (c5 := YKK.getr regs (Z_to_bv 5 21)) (c4 := YKK.getr regs (Z_to_bv 5 20))
        (c3 := YKK.getr regs (Z_to_bv 5 19)) (c2 := YKK.getr regs (Z_to_bv 5 18))
        (c1 := YKK.getr regs (Z_to_bv 5 9)) (c0 := YKK.getr regs (Z_to_bv 5 8))
        (cra := YKK.getr regs (Z_to_bv 5 1));
        [ exact HP0 | lia | reflexivity | reflexivity | ho_lia
        | rewrite unsigned_lit by ho_lia; ho_lia
        | rewrite unsigned_lit by ho_lia; ho_lia
        | rewrite unsigned_lit by ho_lia; exact FR2
        | rewrite unsigned_lit by ho_lia; exact RNG2 ]. }
    intros ms1 ms2 md2' HPOST Heqv HGROW SBM. unfold ho_tail_post in HPOST.
    assert (JI3 : ajournalB HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2' 0)
      by exact (@cgb_j_sbm rc B LAWS HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 md2'
                  JI2 SBM).
    assert (ESW : bv_unsigned (Z_to_bv 64 (spZ regs + -80)) = spZ regs - 80)
      by (rewrite unsigned_lit by ho_lia; lia).
    destruct HPOST as [(Ev & ->) | [(Nv & Hlt & ->) | (Nv & E9 & ->)]].
    + (* the round hit: a0 = i, and the model's answer is i *)
      assert (HR : r = i).
      { destruct HCASE as [(_ & Hr) | (EB & _)]; [exact Hr|].
        exfalso. rewrite (proj1 CMP Ev) in EB. discriminate EB. }
      unfold ho_ret_st in Heqv |- *.
      destruct (decode_eqv_mkst _ _ _ _ Heqv) as (Rx & Ems & Xq).
      rewrite Ems. rewrite GRET.
      apply (ho_close Rx mem2 md2').
      * exact JI3.
      * apply (ho_pres_xeqv _ Rx Xq). apply ho_pres_ret. exact ESW.
      * rewrite (decode_getr_xeqv _ _ Xq (Z_to_bv 5 10)). rewrite HR. reflexivity.
    + (* the round missed and the model goes on: round i + 1 *)
      assert (HL1 : TCb.host_offset_loop n body (i + 1) = Some r).
      { destruct HCASE as [(EB & _) | (_ & HH)]; [|exact HH].
        exfalso. apply Nv. apply CMP. exact EB. }
      unfold ho_call_st in Heqv.
      destruct (decode_eqv_mkst _ _ _ _ Heqv) as (Rx & Ems & Xq).
      rewrite Ems.
      pose proof (fun rz => decode_getr_xeqv _ _ Xq rz) as Gr.
      apply (IH (i + 1) Rx mem2 md2' junk);
        [ lia | lia | exact HL1 | exact JI3 | exact VK2
        | exact FR2 | exact LJ | ].
      unfold ho_regs_at. replace (p + (i + 1)) with (p + i + 1) by lia.
      repeat split.
      all: rewrite (Gr _).
      all: first [ reflexivity
                 | rewrite (HP2 _ ltac:(unfold acallee_saved; lia)); reflexivity ].
    + (* the tenth round missed: a0 = -1, and the model's answer is -1 *)
      assert (HR : r = -1).
      { destruct HCASE as [(EB & _) | (_ & HH)].
        - exfalso. apply Nv. apply CMP. exact EB.
        - assert (En : n = 0%nat) by lia. subst n.
          exact (ho_loop_zero body (i + 1) r HH). }
      unfold ho_ret_st in Heqv |- *.
      destruct (decode_eqv_mkst _ _ _ _ Heqv) as (Rx & Ems & Xq).
      rewrite Ems. rewrite GRET.
      apply (ho_close Rx mem2 md2').
      * exact JI3.
      * apply (ho_pres_xeqv _ Rx Xq). apply ho_pres_ret. exact ESW.
      * rewrite (decode_getr_xeqv _ _ Xq (Z_to_bv 5 10)). rewrite HR. reflexivity.
Qed.

(* ---- the walk ---- *)

Lemma ho_holds :
  SRr tfibsegs W (@cfg_at fx tfibsegs (transportb_sigma TB_host_offset) regs memc mdc)
    (transport_hoff_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).
Proof using All.
  pose proof ho_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof ho_mod as (EBw & HLOOP).
  pose proof ho_len as LB.
  pose proof ho_rdb as RDB. pose proof RDB as (_ & _ & _ & RBm & RB0 & RB63).
  assert (G10 : YKK.getr regs (Z_to_bv 5 10) = w64 p) by exact H10.
  pose proof ho_inner as JI0.
  pose proof JI0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES0 & _).
  assert (STK0 : stk rsegs memc (spZ regs - HOFF_STK) (spZ regs))
    by (apply (ho_stk_present (w_H W)); [ho_lia | ho_lia | intros a Ha; apply HPRES0; lia]).
  assert (RFR : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) (spZ regs - 80) 80).
  { apply (decode_rng_vis W); [ho_lia | ho_lia|]. intros j Hj.
    exact (proj1 (HPRES0 (spZ regs - 80 + j) ltac:(ho_lia))). }
  (* the entry run *)
  eapply decode_run.
  { unfold LCK.ms_of_regs. rewrite G10.
    apply ho_pro_F with (lo := spZ regs - HOFF_STK) (p := p);
      [ exact HP0 | ho_lia | exact STK0
      | change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs); ho_lia
      | exact RFR ]. }
  intros ms0 ms1 md1 HP Heqv HGROW SBM.
  destruct HP as (m1 & junk & -> & MU & WM & ST1 & FR).
  assert (LJ : length junk = 8%nat).
  { pose proof (proj1 (proj1 FR)) as Hwf. unfold ho_fr in Hwf. cbn [cells_wf cell_wf] in Hwf. tauto. }
  assert (JI1 : ajournalB HOFF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W m1 md1 0).
  { apply (ho_journal_pro m1 md1 MU); [exact HGROW | exact SBM]. }
  unfold ho_call_st in Heqv.
  destruct (decode_eqv_mkst _ _ _ _ Heqv) as (Rx & Ems & Xq).
  rewrite Ems.
  pose proof (fun rz => decode_getr_xeqv _ _ Xq rz) as Gr.
  apply (ho_round 10%nat 0 Rx m1 md1 junk);
    [ reflexivity | lia | exact HLOOP | exact JI1
    | exact (ho_vk_munch m1 MU) | unfold ho_frame; exact FR | exact LJ | ].
  unfold ho_regs_at. replace (p + 0) with p by lia.
  repeat split.
  all: rewrite (Gr _).
  all: reflexivity.
Qed.

End Call.
End Walk.

(* The statement of lib/B/Prog/host_offset_cg.v: the runtime cells (HOST's shadow), the rest of HOST's shadow group,
   the allocator and meter laws and the bcmp contract give the contract at TB_host_offset. *)
Theorem transport_host_offset_cg_holds {fx : YKK.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  @transport_host_offset_cg_holds_stmt fx rc B MT.
Proof.
  intros HCELLS HHOFF HOWN HERR LAWS MTL ABCMP.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p r body Bw Bw'.
  intros HJ HRET HRA4 HGP HTP H10 HAL HWLO HWHI HP0 GBB HSRC OWB HROM HM HNEV.
  exact (ho_holds B MT HCELLS HHOFF LAWS MTL ABCMP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
           p r body Bw Bw' HJ HRET HRA4 HGP HTP H10 HAL HWLO HWHI HP0 GBB HSRC OWB HROM HM HNEV).
Qed.
