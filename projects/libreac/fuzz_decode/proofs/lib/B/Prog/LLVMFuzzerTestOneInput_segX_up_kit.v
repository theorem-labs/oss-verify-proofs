(* LLVMFuzzerTestOneInput_segX_up_kit: what the image-B up segment of LLVMFuzzerTestOneInput needs across its calls:
   the memory clauses llvm_b_st_840 and llvm_b_st_96c share (up_mem) and their transfer across a step (up_mem_kept,
   up_mode_kept), the facts of the slot pre it reads (up_base), the frame-pointer chain and the trace an allocator
   call sees (up_chain_pre, up_trace_in), and the transfer of the frame invariant and the memory clauses across a call
   that keeps every byte outside its stack window and a write set (up_win_kept).

   The mode tables' pointer words are constant cells of B (dec_crt_cells, lib/B/Prog/check_round_trip_cg.v), so AR's
   am_const reads the same bytes there at every state; the tables' +4 / +8 words are DEC_RO_RD bytes, which
   dec_rom_view_rd shows as the image's at every state the slot's journal reaches (up_rom_rd, from
   lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_defs.v ex_rom_rd); the local mode at d_F + 32 lies in the fake frame,
   which every call keeps. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs reac_upstream_channels_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_exit_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := decodesegsB0.

(* The memory clauses llvm_b_st_840 and llvm_b_st_96c share. *)
Definition up_mem (cx : dctx) (W : world segs) (mem : word -> option byte) (res mode nch ns : Z) : Prop :=
  dec_b_frs cx (aview segs (w_H W) mem) /\
  dec_b_mode_ok cx W mem mode nch ns /\
  dec_b_fsh cx (aview segs (w_H W) mem) 0 4 /\
  garr8 segs (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
  dec_b_slot cx (aview segs (w_H W) mem) 24 (dec_b_len (d_n cx)) /\
  dec_b_slot cx (aview segs (w_H W) mem) 32 SHADOW_OFF /\
  dec_b_slot cx (aview segs (w_H W) mem) 40 res /\
  dec_b_slot cx (aview segs (w_H W) mem) 80 (res + 50) /\
  dec_b_slot cx (aview segs (w_H W) mem) 112 (d_F cx).

(* The facts of the slot pre (dec_b_base) the segment reads: lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_defs.v
   ex_base's conclusions, at the return address RA the caller passes. *)
Definition up_base (RA : Z) (cx : dctx) : Prop :=
  @achain rc (d_ly cx) (aview segs (w_H (d_W cx)) (d_mem cx)) (d_sp0 cx) (s0Z (d_regs cx)) [] /\
  astk_ok DEC_LLVMF_STK (d_ly cx) (d_sp0 cx) /\ 4096 <= raZ (d_regs cx) /\ raZ (d_regs cx) = RA /\
  st_nev (d_S cx) + DEC_EV_LIB <= EV_MAX /\ blocks_bytes (d_S cx) + DEC_LIVE_LIB <= LIVE_MAX /\
  0 <= d_n cx < 67108864 /\ d_n cx = Z.of_nat (length (d_pl cx)).

(* ---- constant cells ---------------------------------------------------------------------------------- *)

(* A constant cell of B at an image address shows its bytes at every state AR holds of. *)
Lemma up_cell_view : forall ly S W mem md a w v k,
  AR segs B ly S W mem md -> In (ACell (ANum a) w (AV (ANum v))) (as_const B ly) -> (k < w)%nat ->
  aview segs (w_H W) mem (a + Z.of_nat k) = Some (le_byte v w k).
Proof.
intros ly S W mem md a w v k HAR Hin Hk.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as Hc.
unfold cell_holds in Hc. cbn [c_at YG0f.c_val c_w aeval] in Hc. exact (Hc k Hk).
Qed.

(* So two states AR holds of agree there. *)
Lemma up_cell_agree : forall ly S W mem md ly2 S2 W2 mem2 md2 a w v,
  AR segs B ly S W mem md -> AR segs B ly2 S2 W2 mem2 md2 ->
  (forall l, In (ACell (ANum a) w (AV (ANum v))) (as_const B l)) ->
  forall j, 0 <= j < Z.of_nat w -> aview segs (w_H W2) mem2 (a + j) = aview segs (w_H W) mem (a + j).
Proof.
intros ly S W mem md ly2 S2 W2 mem2 md2 a w v HAR HAR2 Hin j Hj.
replace j with (Z.of_nat (Z.to_nat j)) by lia.
rewrite (up_cell_view ly2 S2 W2 mem2 md2 a w v (Z.to_nat j) HAR2 (Hin ly2) ltac:(lia)).
rewrite (up_cell_view ly S W mem md a w v (Z.to_nat j) HAR (Hin ly) ltac:(lia)).
reflexivity.
Qed.

Lemma up_val_mem_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a n v,
  (forall j, 0 <= j < Z.of_nat n -> aview segs H' m' (a + j) = aview segs H m (a + j)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hkn. rewrite <- (Hv k Hkn). apply (mbyte_of_aview segs). apply Hk. lia.
Qed.

(* Two states whose read-only view shows the image at the DEC_RO_RD bytes agree there. *)
Lemma up_ro_agree : forall (W W2 : world segs) mem mem2,
  dec_rom_view_rd W mem -> dec_rom_view_rd W2 mem2 ->
  forall a, dec_in_ro_rd a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a.
Proof. intros W W2 mem mem2 HR HR2 a Ha. rewrite (HR2 a Ha), (HR a Ha). reflexivity. Qed.

(* The +4 / +8 words of the three mode tables are DEC_RO_RD bytes. *)
Lemma up_tab_ro : forall t a, t = 0x20d60 \/ t = 0x20d80 \/ t = 0x20da0 -> t + 4 <= a < t + 12 -> dec_in_ro_rd a.
Proof.
intros t a Ht Ha. unfold dec_in_ro_rd. apply Exists_exists.
exists (t + 4, 8). split; [|unfold in_zr; cbn [fst snd]; lia].
unfold DEC_RO_RD. destruct Ht as [-> | [-> | ->]]; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

(* The scoped read-only view at any state the slot's journal reaches: ex_rom_rd at the frame invariant's journal. *)
Lemma up_rom_rd : forall cx ly S W regs mem md k,
  dec_ro_rd_unowned B -> dec_rom_no_errno B -> rom_view segs (d_W cx) (d_mem cx) ->
  dec_b_core B cx ly S W regs mem md k -> dec_rom_view_rd W mem.
Proof.
intros cx ly S W regs mem md k HO HE HR (HJ & _). exact (ex_rom_rd B cx _ _ _ _ _ _ _ _ HO HE HR HJ).
Qed.

(* The mode clause survives any step after which AR still holds, the read-only view shows the image at both
   states, and the fake frame reads the same. *)
Lemma up_mode_kept : forall cx ly S W mem md ly2 S2 W2 mem2 md2 mode nch ns,
  dec_crt_cells B ->
  AR segs B ly S W mem md -> AR segs B ly2 S2 W2 mem2 md2 ->
  dec_rom_view_rd W mem -> dec_rom_view_rd W2 mem2 ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  dec_b_mode_ok cx W mem mode nch ns -> dec_b_mode_ok cx W2 mem2 mode nch ns.
Proof.
intros cx ly S W mem md ly2 S2 W2 mem2 md2 mode nch ns HC HAR HAR2 HRO HRO2 KF (Hsrc & Hb1 & Hb2 & V4 & V8).
assert (CELL : forall a w v, (forall l, In (ACell (ANum a) w (AV (ANum v))) (as_const B l)) ->
  forall j, 0 <= j < Z.of_nat w -> aview segs (w_H W2) mem2 (a + j) = aview segs (w_H W) mem (a + j))
  by (intros a w v Hin; exact (up_cell_agree ly S W mem md ly2 S2 W2 mem2 md2 a w v HAR HAR2 Hin)).
(* the rows of dec_crt_cells this lemma reads *)
assert (R4 : forall l, In (z8 (ANum (decodeb_obj 4%nat)) 0x20d60) (as_const B l))
  by (intros l; pose proof (HC l) as Hl; decompose [and] Hl; assumption).
assert (R5 : forall l, In (z8 (ANum (decodeb_obj 5%nat)) 0x20da0) (as_const B l))
  by (intros l; pose proof (HC l) as Hl; decompose [and] Hl; assumption).
assert (R6 : forall l, In (z8 (ANum (decodeb_obj 6%nat)) 0x20d80) (as_const B l))
  by (intros l; pose proof (HC l) as Hl; decompose [and] Hl; assumption).
(* a table: its pointer word reads the same before and after (a constant cell), and its two fields too (DEC_RO_RD
   bytes, the image at both states) *)
assert (TAB : forall q t, t = 0x20d60 \/ t = 0x20d80 \/ t = 0x20da0 -> (forall l, In (z8 (ANum q) t) (as_const B l)) ->
  rdword (aview segs (w_H W) mem) q = Some mode ->
  rdword (aview segs (w_H W2) mem2) q = Some mode /\
  val_mem segs (mrestrict (w_H W2) mem2) (mode + 4) 4%nat (nch mod 2 ^ 32) /\
  val_mem segs (mrestrict (w_H W2) mem2) (mode + 8) 4%nat (ns mod 2 ^ 32)).
{ intros q t Ht Rq Hq.
  assert (Htr : 0 <= t < 18446744073709551616) by (destruct Ht as [-> | [-> | ->]]; lia).
  assert (Hw : rdword (aview segs (w_H W) mem) q = Some t).
  { eapply rdword_cell; [change (2 ^ 64) with 18446744073709551616; exact Htr|].
    exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ (Rq ly)). }
  rewrite Hw in Hq. injection Hq as Hq. subst mode.
  split; [rewrite <- Hw; apply rdword_ext; intros j Hj; apply (CELL q 8%nat t Rq); lia|].
  split; apply (up_val_mem_kept (w_H W) (w_H W2) mem mem2); [| exact V4 | | exact V8];
    intros j Hj; apply (up_ro_agree W W2 mem mem2 HRO HRO2); apply (up_tab_ro t); first [exact Ht | lia]. }
destruct Hsrc as [H4 | [H5 | [H6 | Hloc]]].
- destruct (TAB (decodeb_obj 4%nat) 0x20d60 (or_introl eq_refl) R4 H4) as (Q1 & Q2 & Q3).
  split; [left; exact Q1|]. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Q2 | exact Q3].
- destruct (TAB (decodeb_obj 5%nat) 0x20da0 (or_intror (or_intror eq_refl)) R5 H5) as (Q1 & Q2 & Q3).
  split; [right; left; exact Q1|]. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Q2 | exact Q3].
- destruct (TAB (decodeb_obj 6%nat) 0x20d80 (or_intror (or_introl eq_refl)) R6 H6) as (Q1 & Q2 & Q3).
  split; [right; right; left; exact Q1|]. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Q2 | exact Q3].
- subst mode. split; [right; right; right; reflexivity|]. split; [exact Hb1|]. split; [exact Hb2|].
  split; apply (up_val_mem_kept (w_H W) (w_H W2) mem mem2); [| exact V4 | | exact V8];
    intros j Hj; apply KF; lia.
Qed.

(* The memory clauses survive a step after which AR still holds, the read-only view shows the image at both states,
   and the spill area, the fake frame, its shadow and the copy read the same. *)
Lemma up_mem_kept : forall cx ly S W mem md ly2 S2 W2 mem2 md2 res mode nch ns,
  dec_crt_cells B ->
  AR segs B ly S W mem md -> AR segs B ly2 S2 W2 mem2 md2 ->
  dec_rom_view_rd W mem -> dec_rom_view_rd W2 mem2 ->
  d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 ->
  (forall a, d_sp1 cx <= a < d_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall i, 0 <= i < Z.of_nat (length (d_body cx)) ->
     aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) mem (res + i)) ->
  up_mem cx W mem res mode nch ns -> up_mem cx W2 mem2 res mode nch ns.
Proof.
intros cx ly S W mem md ly2 S2 W2 mem2 md2 res mode nch ns HC HAR HAR2 HRO HRO2 Hsp1 KS KF KH KR
  ((F0 & F8 & F16) & Hmode & (H0 & H4 & H5 & H6) & Hg & S24 & S32 & S40 & S80 & S112).
assert (SLOT : forall off v, 0 <= off <= 112 -> dec_b_slot cx (aview segs (w_H W) mem) off v ->
  dec_b_slot cx (aview segs (w_H W2) mem2) off v).
{ intros off v Hoff Hs. unfold dec_b_slot in *. rewrite <- Hs. apply rdword_ext. intros j Hj. apply KS. lia. }
split; [split; [apply SLOT; [lia | exact F0] | split; [apply SLOT; [lia | exact F8] | apply SLOT; [lia | exact F16]]]|].
split; [exact (up_mode_kept cx ly S W mem md ly2 S2 W2 mem2 md2 mode nch ns HC HAR HAR2 HRO HRO2 KF Hmode)|].
split.
{ split; [intros i Hi; rewrite KH by lia; exact (H0 i Hi)|].
  split; [rewrite KH by lia; exact H4|]. split; [rewrite KH by lia; exact H5|].
  intros i Hi; rewrite KH by lia; exact (H6 i Hi). }
split; [apply (ex_garr8_kept (w_H W) (w_H W2) mem mem2); [rewrite length_map; exact KR | exact Hg]|].
split; [apply SLOT; [lia | exact S24]|]. split; [apply SLOT; [lia | exact S32]|].
split; [apply SLOT; [lia | exact S40]|]. split; [apply SLOT; [lia | exact S80] | apply SLOT; [lia | exact S112]].
Qed.

(* The frame-pointer chain at a call of this function: s0 = the entry sp, the call's sp = d_sp1. *)
Lemma up_chain_pre : forall RA cx ly S W regs mem md k regsT,
  up_base RA cx -> dec_b_core B cx ly S W regs mem md k ->
  spZ regsT = d_sp1 cx -> s0Z regsT = d_sp0 cx -> 4096 <= raZ regsT ->
  chain_pre ly (aview segs (w_H W) mem) regsT (ex_ch cx).
Proof.
intros RA cx ly S W regs mem md k regsT (Hch & Hstk & Hra4 & _) Hcore Hsp Hs0 Hraz.
pose proof (ex_achain B cx ly S W regs mem md k Hch Hstk Hra4 Hcore) as Hach.
pose proof Hcore as (HJ & _ & _ & _ & _ & Hsp1r & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
apply (achain_chain_pre ly _ (d_sp1 cx) (d_sp0 cx) (ex_ch cx) regsT Hach); [rewrite Hsp; lia | exact Hs0 | exact Hraz].
Qed.

(* The trace an allocator call of this function records is one dec_llvmf_utraces lists. *)
Lemma up_trace_in : forall RA cx (regsT : bvmap 5 word) pc0 (U : list (list Z)) r,
  up_base RA cx -> raZ regsT = r ->
  (forall sp, In sp [[]; [RA]] -> In (dec_utrace pc0 (r :: sp)) U) ->
  In (call_trace0 pc0 regsT (ex_ch cx)) U.
Proof.
intros RA cx regsT pc0 U r (_ & _ & _ & HRA & _) Hr HU.
rewrite call_trace_of_spine, Hr. unfold ex_ch.
destruct (d_sp0 cx + 16 <? ly_top (d_ly cx)); cbn [spine map fst snd].
- rewrite HRA. exact (HU [RA] ltac:(right; left; reflexivity)).
- exact (HU [] ltac:(left; reflexivity)).
Qed.

(* A call that keeps every byte outside its stack window [d_sp1 - 4096, d_sp1) and a write set Wr, at the same
   layout and allocator state (a leaf, through lib/B/Prog/LLVMFuzzerTestOneInput_leafb.v dec_leafb_journal, or an
   intrinsic, through lib/A/Prog/YC85.v aj_intrin_atS): the frame invariant and the memory clauses hold at its
   return when Wr misses the spill area, the fake frame and its shadow, the copy and the payload. The read-only view
   at both states comes from the two journals (up_rom_rd / ex_rom_rd). *)
Lemma up_win_kept : forall cx ly S W regs mem md k regs2 mem2 md2 res mode nch ns (Wr : Z -> Prop),
  AR_laws segs B -> dec_crt_cells B ->
  dec_ro_rd_unowned B -> dec_rom_no_errno B -> rom_view segs (d_W cx) (d_mem cx) ->
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  dec_b_core B cx ly S W regs mem md k ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W mem2 md2 k ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 4096 <= a < d_sp1 cx) -> ~ Wr a ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  (forall a, d_sp1 cx <= a < d_sp0 cx -> ~ Wr a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> ~ Wr a) ->
  (forall a, d_SH cx <= a < d_SH cx + 8 -> ~ Wr a) ->
  (forall i, 0 <= i < Z.of_nat (length (d_pl cx)) -> ~ Wr (d_p cx + i)) ->
  In (res, dec_b_len (d_n cx)) (ablocks B ly S) ->
  (forall i, 0 <= i < req_size (dec_b_len (d_n cx)) -> ~ Wr (res + i)) ->
  up_mem cx W mem res mode nch ns ->
  dec_b_core B cx ly S W regs2 mem2 md2 k /\ up_mem cx W mem2 res mode nch ns.
Proof.
intros cx ly S W regs mem md k regs2 mem2 md2 res mode nch ns Wr LAWS HC HO HE HR Hnlen Hcore HJ2 HP Heff Hpres
  NS NF NH NP Hres NR Hmem.
pose proof Hcore as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof (proj1 HJ2) as HAR2.
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
destruct (frames_bounds segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin0) as (Hb1 & Hb2 & _).
rewrite EFA in Hb1. change (fs_frame_bytes DEC_FCLASS) with 64 in Hb2. rewrite EFA in Hb2.
assert (Hwin : forall a, a < alloc_ceiling -> ~ (d_sp1 cx - 4096 <= a < d_sp1 cx)) by (intros a Ha Hw; lia).
assert (KS : forall a, d_sp1 cx <= a < d_sp0 cx -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha. apply Heff; [lia | lia | exact (NS a Ha)]. }
assert (KF : forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha. apply Heff; [lia | apply Hwin; lia | exact (NF a Ha)]. }
assert (HFd : 0 <= d_F cx / 8 <= alloc_ceiling / 8).
{ split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]. }
assert (HSHb : d_SH cx + 8 <= alloc_ceiling).
{ unfold d_SH, shadow_addr, SHADOW_OFF. lia. }
assert (KH : forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha. apply Heff; [unfold d_SH, shadow_addr, SHADOW_OFF in *; lia
  | apply Hwin; lia | exact (NH a Ha)]. }
destruct (al_blocks _ _ LAWS ly S W mem md res _ HAR Hres) as (_ & Hr4096 & Hrc & _).
pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(unfold dec_b_len; lia)) as Hrq.
assert (KR : forall i, 0 <= i < req_size (dec_b_len (d_n cx)) ->
  aview segs (w_H W) mem2 (res + i) = aview segs (w_H W) mem (res + i)).
{ intros i Hi. apply Heff; [lia | apply Hwin; lia | exact (NR i Hi)]. }
assert (KP : forall r : Z, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) by exact HP.
split.
- apply (ex_core_kept B cx ly S W regs mem md k ly S W regs2 mem2 md2 k Hcore HJ2 Hfrs).
  + exact (KP 8 ltac:(unfold acallee_saved; lia)).
  + exact (KP 9 ltac:(unfold acallee_saved; lia)).
  + unfold spZ. exact (f_equal bv_unsigned (KP 2 ltac:(unfold acallee_saved; lia))).
  + exact (KP 3 ltac:(unfold acallee_saved; lia)).
  + exact (KP 4 ltac:(unfold acallee_saved; lia)).
  + intros a Ha. apply KS. lia.
  + exact KF.
  + intros a Ha. apply Hpres. exact (HFpres a Ha).
  + exact Hpay.
  + intros i Hi. destruct (Z.lt_ge_cases 0 (d_n cx)) as [Hn0 | Hn0].
    * destruct (al_blocks _ _ LAWS ly S W mem md (d_p cx) (d_n cx) HAR (Hpay Hn0)) as (_ & Hp4096 & Hpc & _).
      pose proof (req_size_pos (d_n cx) ltac:(lia)).
      assert (Hi' : i < req_size (d_n cx)) by lia.
      apply Heff; [split; lia | apply Hwin; lia | exact (NP i Hi)].
    * exfalso. lia.
- apply (up_mem_kept cx ly S W mem md ly S W mem2 md2 res mode nch ns HC HAR HAR2
    (up_rom_rd cx ly S W regs mem md k HO HE HR Hcore) (ex_rom_rd B cx _ _ _ _ _ _ _ _ HO HE HR HJ2) Hsp1r KS KF KH).
  + intros i Hi. apply KR. split; [lia|].
    assert (Hlb : Z.of_nat (length (d_body cx)) <= dec_b_len (d_n cx)).
    { unfold d_body, dec_b_len, dec_b_u. rewrite length_skipn. lia. }
    lia.
  + exact Hmem.
Qed.
End d.
