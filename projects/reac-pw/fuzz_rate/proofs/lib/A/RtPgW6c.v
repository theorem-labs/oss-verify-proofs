(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the walk piece "ent_build C"
   of LLVMFuzzerTestOneInput (0x80714), RtPgSeg's rs_piece_W6c_stmt: from the cut D at the switch entry of
   kind % 10 = 6 (0x81880), 7 (0x81754) or 8 (0x818d0) to the cut J 0x81e00 (pod.h:340-366). Proves no function
   (kind: segment lemma).

   THE CHAIN. At D (RtPgSeg rs_cut_D) w6c_prep reads the block statements' premises (lib/A/RtPgW6cBase.v): the
   context (the journal, the frame geometry, rom_view by RtPgW6cKit.rs_rom_now), the registers and cells of rs_L_D,
   the input at the cursor (RtPgW6cKit.rs_in_now and the suffix), e's 104 zeros and the two tables' shadow (the
   registered globals of rs_pre, carried by rs_core_kept and rs_wr_shadow). The case's head (RtPgW6c6 / 7 / 8) runs to
   the intrinsic's entry; w6c_src_ok and w6c_hdr_bytes give its tail's premises (lib/A/RtPgW6cTail.v); the tail ends
   at J in w6c_jpost; w6c_to_J turns that into RtPgSeg's rs_cut_J (the journal-and-frame part, the location list
   through the kept registers and the real frame's cells, the frame's shadow and the first block kept, e = ent_mem
   of Model.ent_build's pod of the turn's input) and applies the continuation rs_from_J. The heads and tails are this
   file's Section hypotheses until the end, where the proved lemmas discharge them. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgMem RtPgSteps RtPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgW6cKit RtPgW6cBase RtPgW6cTail.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgW6c6 RtPgW6c7 RtPgW6c8.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== registers ======================================== *)
Lemma w6c_regZ : forall (regs : bvmap 5 word) (q : bv 5) r, bv_unsigned q = r -> getr regs (Z_to_bv 5 r) = getr regs q.
Proof. intros regs q r <-. rewrite (Z_to_bv_bv_unsigned 5 q). reflexivity. Qed.
Lemma w6c_getrZ : forall (regs regs' : bvmap 5 word) (q : bv 5) r v, bv_unsigned q = r ->
getr regs (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r) -> getr regs' q = v -> getr regs q = v.
Proof. intros regs regs' q r v Hq E H. rewrite <- (w6c_regZ regs q r Hq), E, (w6c_regZ regs' q r Hq). exact H. Qed.
Lemma w6c_notin : forall (r : bv 5) (l : list (bv 5)), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros r l H Hin. induction l as [|c l IH]; [exact Hin|]. cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)]. unfold bv_eqb in H1. rewrite Z.eqb_refl in H1. discriminate H1.
Qed.
Lemma w6c_nz : forall r : bv 5, (bv_unsigned r =? 0) = false -> bv_unsigned r <> 0.
Proof. intros r H. apply Z.eqb_neq. exact H. Qed.
(* a register a block keeps (outside clob) *)
Ltac w6c_kept HK := rewrite HK; [| apply w6c_nz; reflexivity | apply w6c_notin; reflexivity].
(* the location lists of the cuts, as literal lists, and membership in them *)
Ltac w6c_unf := cbv [rs_L_D rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc rs_Hc rs_podc app].
Ltac w6c_mem := cbn [In]; repeat first [left; reflexivity | right].

(* the registers the cut J keeps, as RtPgSeg names them (Z) and as the blocks name them (bv 5) *)
Definition w6c_keepZ : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27].
Lemma w6c_keep_clob : forall q, In q w6c_keep -> bv_unsigned q <> 0 /\ ~ In q w6c_clob67 /\ ~ In q w6c_clob8.
Proof.
intros q Hq. cbv [w6c_keep In] in Hq.
repeat (destruct Hq as [<-|Hq];
  [split; [apply w6c_nz; reflexivity | split; apply w6c_notin; reflexivity] |]).
destruct Hq.
Qed.
Lemma w6c_keepZ_bv : forall (regs regs' : bvmap 5 word), (forall q, In q w6c_keep -> getr regs' q = getr regs q) ->
forall r, In r w6c_keepZ -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros regs regs' HK r Hr. apply HK. cbv [w6c_keepZ In] in Hr.
repeat (destruct Hr as [<-|Hr]; [cbv [w6c_keep In]; repeat (first [left; apply bv_eq; reflexivity | right]) |]).
destruct Hr.
Qed.

(* ======================================== location lists ======================================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma w6c_val_mod : forall m a v, val_mem rsegs m a 8 (v mod 2 ^ 64) <-> val_mem rsegs m a 8 v.
Proof.
intros m a v. unfold val_mem.
assert (E : forall k, YO0f.le_byte (v mod 2 ^ 64) 8 k = YO0f.le_byte v 8 k).
{ intros k. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
split; intros H k Hk; specialize (H k Hk); [rewrite <- E | rewrite E]; exact H.
Qed.
Lemma w6c_at_get : forall H mem regs e (L : list (rt_loc * Z)) l v,
rs_at rsegs H mem regs e L -> In (l, v) L -> rt_at rsegs H mem regs e l v.
Proof. intros H mem regs e L l v A Hin. unfold rs_at in A. rewrite Forall_forall in A. exact (A _ Hin). Qed.
Lemma w6c_at_reg : forall H mem regs e (L : list (rt_loc * Z)) r v (q : bv 5),
rs_at rsegs H mem regs e L -> In (LReg r, v) L -> bv_unsigned q = r -> getr regs q = w64 v.
Proof.
intros H mem regs e L r v q A Hin Hq. rewrite <- (w6c_regZ regs q r Hq).
exact (w6c_at_get H mem regs e L (LReg r) v A Hin).
Qed.
Lemma w6c_at_cell8 : forall H mem regs e (L : list (rt_loc * Z)) b o v,
rs_at rsegs H mem regs e L -> In (LCell b o, v) L -> val_mem rsegs (mrestrict H mem) (rt_xv e b + o) 8 v.
Proof. intros H mem regs e L b o v A Hin. apply w6c_val_mod. exact (w6c_at_get H mem regs e L (LCell b o) v A Hin). Qed.
Lemma w6c_fsub : forall {X} (P : X -> Prop) (L L' : list X), Forall P L -> Forall (fun f => In f L \/ P f) L' -> Forall P L'.
Proof.
intros X P L L' HL H. rewrite Forall_forall in *. intros f Hf.
destruct (H f Hf) as [Hi|Hp]; [exact (HL f Hi) | exact Hp].
Qed.

(* a list whose registers are kept and whose cells are R-relative cells in [R, R + 0x180) *)
Definition w6c_okloc (f : rt_loc * Z) : bool :=
match fst f with
| LReg r => existsb (Z.eqb r) w6c_keepZ
| LCell XR o => (0 <=? o) && (o <=? 0x178)
| LCell _ _ => false
end.
Lemma w6c_keeps_L : forall H mem H' mem' regs regs' e (L : list (rt_loc * Z)),
forallb w6c_okloc L = true ->
(forall r, In r w6c_keepZ -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall o i, 0 <= o <= 0x178 -> 0 <= i < 8 -> aview rsegs H' mem' (q_R e + o + i) = aview rsegs H mem (q_R e + o + i)) ->
rs_at rsegs H mem regs e L -> rs_at rsegs H' mem' regs' e L.
Proof.
intros H mem H' mem' regs regs' e L Hb Hr Hc A. unfold rs_at in *.
apply (rtm_atl_kept rsegs H mem H' mem' regs regs' e L A).
intros f Hf. rewrite forallb_forall in Hb. specialize (Hb f Hf).
destruct f as [[r|b o] v].
- cbn [fst w6c_okloc] in Hb. cbn [fst rtm_keeps]. apply Hr.
  apply existsb_exists in Hb as (x & Hx & Hxe). apply Z.eqb_eq in Hxe. subst x. exact Hx.
- cbn [fst rtm_keeps]. destruct b; cbn [fst w6c_okloc] in Hb; try discriminate Hb.
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  intros i Hi. cbn [rt_xv]. apply Hc; lia.
Qed.

(* ======================================== the input and its shadow ======================================== *)
Lemma w6c_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> 0 <= x -> x <= x' -> x' + n' <= x + n ->
0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H Hx0 H1 H2 H3 s Hs. apply H.
assert (M : forall a b, 0 <= a -> a <= b -> shadow_addr a / 8 * 8 <= shadow_addr b / 8 * 8).
{ intros a b Ha Hab. unfold shadow_addr.
  assert (a / 8 <= b / 8) by (apply Z.div_le_mono; lia).
  assert ((SHADOW_OFF + a / 8) / 8 <= (SHADOW_OFF + b / 8) / 8) by (apply Z.div_le_mono; lia). lia. }
pose proof (M x x' Hx0 H1). pose proof (M (x' + n' - 1) (x + n - 1) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma w6c_src_bytes : forall H mem a (r : list byte) j m,
rtm_bytes rsegs H mem a r -> rtm_bytes rsegs H mem (a + Z.of_nat (Nat.min j (length r))) (firstn m (skipn j r)).
Proof.
intros H mem a r j m Hb.
pose proof (proj1 (rtm_bytes_app rsegs H mem a (firstn j r) (skipn j r))) as Happ. rewrite firstn_skipn in Happ.
destruct (Happ Hb) as [_ H2]. rewrite length_firstn in H2.
pose proof (proj1 (rtm_bytes_app rsegs H mem (a + Z.of_nat (Nat.min j (length r))) (firstn m (skipn j r)) (skipn m (skipn j r)))) as Happ2.
rewrite firstn_skipn in Happ2. destruct (Happ2 H2) as [H3 _]. exact H3.
Qed.
(* a byte of e's header after the head's two stores is present *)
Lemma w6c_present_hdr : forall H mem F ty sz a,
val_mem rsegs (mrestrict H mem) (F + 0xf0) 4 ty -> val_mem rsegs (mrestrict H mem) (F + 0xf4) 4 sz ->
F + 0xf0 <= a < F + 0xf8 -> aview rsegs H mem a <> None.
Proof.
intros H mem F ty sz a Vt Vs Ha. unfold aview.
destruct (Z_lt_le_dec a (F + 0xf4)) as [Hl|Hl].
- pose proof (Vt (Z.to_nat (a - (F + 0xf0))) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
  replace (F + 0xf0 + (a - (F + 0xf0))) with a in Hb by lia. rewrite Hb. cbn. discriminate.
- pose proof (Vs (Z.to_nat (a - (F + 0xf4))) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
  replace (F + 0xf4 + (a - (F + 0xf4))) with a in Hb by lia. rewrite Hb. cbn. discriminate.
Qed.

(* the memcpy's source after a head: the m bytes after the first j of the input, kept by the head *)
Lemma w6c_src_ok : forall (W : world rsegs) memD memT R F c (r : list byte) (j m : nat) ty sz,
w6c_in W memD R F c r -> in_app F 512 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w6c_hdr_wr F a -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memD a) ->
val_mem rsegs (mrestrict (w_H W) memT) (F + 0xf0) 4 ty -> val_mem rsegs (mrestrict (w_H W) memT) (F + 0xf4) 4 sz ->
rtm_bytes rsegs (w_H W) memT (c + Z.of_nat (Nat.min j (length r))) (firstn m (skipn j r)) /\
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF (c + Z.of_nat (Nat.min j (length r)))
  (Z.of_nat (length (firstn m (skipn j r)))) /\
(0 < Z.of_nat (length (firstn m (skipn j r))) ->
 shadow_hull_vis (aview rsegs (w_H W) memT) (c + Z.of_nat (Nat.min j (length r))) (Z.of_nat (length (firstn m (skipn j r))))) /\
amem_range (c + Z.of_nat (Nat.min j (length r))) (Z.of_nat (length (firstn m (skipn j r)))) /\
0 <= c + Z.of_nat (Nat.min j (length r)) /\
c + Z.of_nat (Nat.min j (length r)) + Z.of_nat (length (firstn m (skipn j r))) <= 2 ^ 63 /\
(forall a, c + Z.of_nat (Nat.min j (length r)) <= a < c + Z.of_nat (Nat.min j (length r)) + Z.of_nat (length (firstn m (skipn j r))) ->
 ~ (R - ESTACK <= a < R) /\ ~ (F + 0xf0 <= a < F + 0x158)).
Proof.
intros W memD memT R F c r j m ty sz (HgI & HraI & HhI & Hc1 & Hctop & HamI & HdisI) HFapp HmT Vty Vsz.
assert (Hlen : (Nat.min j (length r) + length (firstn m (skipn j r)) <= length r)%nat).
{ rewrite length_firstn, length_skipn. lia. }
set (x0 := c + Z.of_nat (Nat.min j (length r))) in *.
set (n0 := Z.of_nat (length (firstn m (skipn j r)))) in *.
assert (Hin : forall x, x0 <= x < x0 + n0 -> c <= x < c + Z.of_nat (length r)) by (intros x Hx; subst x0 n0; lia).
assert (Hx64 : forall x, c <= x < c + Z.of_nat (length r) -> 0 <= x < kHighMemEnd)
  by (intros x Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
assert (HkeepI : forall x, c <= x < c + Z.of_nat (length r) -> aview rsegs (w_H W) memT x = aview rsegs (w_H W) memD x).
{ intros x Hx. pose proof (Hx64 x Hx) as Hb. apply HmT; [unfold kHighMemEnd in Hb; lia |].
  unfold w6c_hdr_wr. destruct (HdisI x Hx) as (_ & _ & _ & _ & D5). lia. }
assert (HkeepS : forall x, c <= x < c + Z.of_nat (length r) ->
  aview rsegs (w_H W) memT (shadow_of_addr SHADOW_OFF x) = aview rsegs (w_H W) memD (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (Hx64 x Hx) as Hb. pose proof (rtm_shadow_band x Hb) as Hsb. apply HmT.
  - unfold kLowMemEnd, kHighMemBeg in Hsb. lia.
  - unfold w6c_hdr_wr. pose proof (rtm_shadow_not_app x F 512 Hb HFapp). lia. }
split.
{ apply (rtm_bytes_kept rsegs (w_H W) memD (w_H W) memT); [exact (w6c_src_bytes _ _ _ _ _ _ HgI)|].
  intros x Hx. apply HkeepI. apply Hin. exact Hx. }
split.
{ intros x Hx. destruct (HraI x ltac:(pose proof (Hin x Hx); lia)) as (s & Hs & Ho). exists s.
  split; [rewrite (HkeepS x (Hin x Hx)); exact Hs | exact Ho]. }
split.
{ intros Hn. apply (rtm_hull_kept rsegs (w_H W) memD (w_H W) memT).
  - apply (w6c_hull_sub _ c (Z.of_nat (length r))); [apply HhI; lia | lia | lia | lia | lia].
  - intros s Hs Hnone.
    assert (Hsb : SHADOW_OFF <= s < kHighMemBeg).
    { pose proof (Hx64 x0 ltac:(pose proof (Hin x0); lia)). pose proof (Hx64 (x0 + n0 - 1) ltac:(pose proof (Hin (x0 + n0 - 1)); lia)).
      unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *.
      pose proof (Z.div_pos x0 8 ltac:(lia) ltac:(lia)).
      assert (2147450880 <= (2147450880 + x0 / 8) / 8 * 8).
      { assert (268431360 <= (2147450880 + x0 / 8) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
      assert ((x0 + n0 - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
      assert ((2147450880 + (x0 + n0 - 1) / 8) / 8 < 2199291686912) by (apply Z.div_lt_upper_bound; lia).
      lia. }
    rewrite HmT; [exact Hnone | unfold SHADOW_OFF, kHighMemBeg in Hsb; lia |].
    unfold w6c_hdr_wr. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
split; [unfold amem_range in *; subst x0 n0; lia|].
split; [subst x0; lia|].
split; [subst x0 n0; lia|].
intros a Ha. destruct (HdisI a (Hin a Ha)) as (D1 & _ & _ & _ & D5).
split; [unfold ESTACK, T_SEG_STK, ASTACK in *; lia | lia].
Qed.

(* e's 104 bytes after the head: type and size, then the 96 zeros of the dispatch's memset *)
Lemma w6c_hdr_bytes : forall H mem H' mem' F ty sz,
rtm_bytes rsegs H mem (F + 0xf0) (zeros 104) ->
val_mem rsegs (mrestrict H' mem') (F + 0xf0) 4 ty -> val_mem rsegs (mrestrict H' mem') (F + 0xf4) 4 sz ->
(forall a, F + 0xf8 <= a < F + 0x158 -> aview rsegs H' mem' a = aview rsegs H mem a) ->
rtm_bytes rsegs H' mem' (F + 0xf0) (le32 ty ++ le32 sz ++ zeros 96).
Proof.
intros H mem H' mem' F ty sz HZ Vt Vs K.
apply rtm_bytes_app. split; [unfold le32; apply rtm_bytes_of_val; exact Vt|].
rewrite length_le32. apply rtm_bytes_app. split.
{ replace (F + 0xf0 + Z.of_nat 4) with (F + 0xf4) by lia. unfold le32. apply rtm_bytes_of_val. exact Vs. }
rewrite length_le32.
pose proof (rtm_bytes_slice rsegs _ _ _ (zeros 104) 8 96 HZ ltac:(rewrite length_zeros; lia)) as HZ1.
change (rtm_slice (zeros 104) 8 96) with (zeros 96) in HZ1.
replace (F + 0xf0 + Z.of_nat 4 + Z.of_nat 4) with (F + 0xf0 + Z.of_nat 8) by lia.
apply (rtm_bytes_kept rsegs _ _ _ _ _ _ HZ1).
intros x Hx. rewrite length_zeros in Hx. apply K. lia.
Qed.

(* ======================================== the model ======================================== *)
Lemma w6c_ent6 : forall (b : byte) r, bv_unsigned b mod 10 = 6 ->
ent_build (b :: r) =
(Ent (w6c_ty6 (fst (fuzz_u8 r))) (w6c_sz6 (w6c_ty6 (fst (fuzz_u8 r))))
  (firstn (Z.to_nat (w6c_sz6 (w6c_ty6 (fst (fuzz_u8 r))))) (snd (fuzz_u8 r)) ++
   zeros (Z.to_nat (w6c_sz6 (w6c_ty6 (fst (fuzz_u8 r)))) -
          length (firstn (Z.to_nat (w6c_sz6 (w6c_ty6 (fst (fuzz_u8 r))))) (snd (fuzz_u8 r))))),
 skipn (Z.to_nat (w6c_sz6 (w6c_ty6 (fst (fuzz_u8 r))))) (snd (fuzz_u8 r))).
Proof.
intros b r H. unfold ent_build. change (fuzz_u8 (b :: r)) with (bv_unsigned b, r). cbv beta iota zeta.
rewrite H. change (Z.to_nat 6) with 6%nat. cbv beta iota zeta.
destruct (fuzz_u8 r) as [t r1]. reflexivity.
Qed.
Lemma w6c_ent7 : forall (b : byte) r, bv_unsigned b mod 10 = 7 ->
ent_build (b :: r) =
(Ent (fst (fuzz_u8 r) mod 21) (fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12)
  (firstn (Z.to_nat (fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12)) (snd (fuzz_u8 (snd (fuzz_u8 r)))) ++
   zeros (Z.to_nat (fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12) -
          length (firstn (Z.to_nat (fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12)) (snd (fuzz_u8 (snd (fuzz_u8 r))))))),
 skipn (Z.to_nat (fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12)) (snd (fuzz_u8 (snd (fuzz_u8 r))))).
Proof.
intros b r H. unfold ent_build. change (fuzz_u8 (b :: r)) with (bv_unsigned b, r). cbv beta iota zeta.
rewrite H. change (Z.to_nat 7) with 7%nat. cbv beta iota zeta.
destruct (fuzz_u8 r) as [t r1]. cbn [fst snd]. destruct (fuzz_u8 r1) as [s r2]. reflexivity.
Qed.
Lemma w6c_ent8 : forall (b : byte) r, bv_unsigned b mod 10 = 8 ->
ent_build (b :: r) =
(Ent (w6c_ty8 (fst (fuzz_u8 r))) (fst (w6c_sz8 (w6c_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r))))
  (zeros (Z.to_nat (fst (w6c_sz8 (w6c_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r)))))),
 snd (w6c_sz8 (w6c_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r)))).
Proof.
intros b r H. unfold ent_build. change (fuzz_u8 (b :: r)) with (bv_unsigned b, r). cbv beta iota zeta.
rewrite H. change (Z.to_nat 8) with 8%nat. cbv beta iota zeta.
destruct (fuzz_u8 r) as [t r1]. cbn [fst snd]. unfold w6c_sz8, w6c_ty8.
destruct (nth (Z.to_nat (t mod 4)) Tables.t8 0 =? POD_STRING) eqn:E.
- apply Z.eqb_eq in E. cbn [fst snd]. rewrite E. reflexivity.
- destruct (fuzz_u8 r1) as [s r2]. reflexivity.
Qed.
Lemma w6c_sz6_rng : forall ty, 0 <= w6c_sz6 ty <= 8.
Proof. intros ty. unfold w6c_sz6. destruct (ty =? POD_NONE); [lia|]. destruct (ty =? POD_ID); lia. Qed.
Lemma w6c_sz8_rng : forall ty r1, 0 <= fst (w6c_sz8 ty r1) < 4.
Proof. intros ty r1. unfold w6c_sz8. destruct (ty =? POD_STRING); cbn [fst]; [lia|]. apply Z.mod_pos_bound. lia. Qed.

(* ======================================== the suffix ======================================== *)
Lemma w6c_suffix_skip : forall rest r n, rs_suffix rest r -> rs_suffix rest (skipn n r).
Proof.
intros rest r n (j & Hj & ->). rewrite skipn_skipn.
destruct (Nat.le_gt_cases (n + j) (length rest)) as [Hle|Hgt].
- exists (n + j)%nat. split; [exact Hle | reflexivity].
- exists (length rest). split; [lia|]. rewrite !skipn_all2 by lia. reflexivity.
Qed.
Lemma w6c_suffix_tl : forall rest b r', rs_suffix rest (b :: r') -> rs_suffix rest r'.
Proof.
intros rest b r' (j & Hj & E). exists (S j).
assert (Hl : length (skipn j rest) = S (length r')) by (rewrite <- E; reflexivity).
rewrite length_skipn in Hl. split; [lia|].
replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, <- E. reflexivity.
Qed.
Lemma w6c_u8_rest : forall r, snd (fuzz_u8 r) = skipn 1 r.
Proof. intros [|b r]; reflexivity. Qed.
Lemma w6c_sz8_suf : forall rest ty r1, rs_suffix rest r1 -> rs_suffix rest (snd (w6c_sz8 ty r1)).
Proof.
intros rest ty r1 H. unfold w6c_sz8. destruct (ty =? POD_STRING); cbn [snd]; [exact H|].
rewrite w6c_u8_rest. apply w6c_suffix_skip. exact H.
Qed.
Lemma w6c_sz8_len : forall ty r1, (length (snd (w6c_sz8 ty r1)) <= length r1)%nat.
Proof.
intros ty r1. unfold w6c_sz8. destruct (ty =? POD_STRING); cbn [snd]; [lia|].
rewrite w6c_u8_rest, length_skipn. lia.
Qed.

(* ======================================== pp's image ======================================== *)
Lemma w6c_pc_ents_wf : forall sh ps es, Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) ->
Forall ent_wf es -> (length es <= 32)%nat ->
(length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\ Forall ent_wf (pc_ents (PbCut sh ps (Some es))).
Proof.
intros sh ps es Hk He Hes Hl. unfold pc_ents. cbn [pc_props pc_open].
destruct (first_params ps) as [[iv|es']|] eqn:E.
- split; [cbn; lia | constructor].
- unfold first_params in E. destruct (find _ _) as [kv|] eqn:F; [|discriminate]. cbn in E. injection E as E.
  apply find_some in F as [Hin _]. split.
  + rewrite Forall_forall in Hk. specialize (Hk kv Hin). rewrite E in Hk. exact Hk.
  + apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite E in He. exact He.
- split; [exact Hl | exact Hes].
Qed.
Lemma w6c_pp_len : forall sh ps es, rs_wf sh ps -> Forall ent_wf es -> (length es < 32)%nat ->
Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE.
Proof.
intros sh ps es (_ & Hkv & Hae & Hlp) Hes Hle.
assert (Hpv : Forall (fun kv => pval_wf (snd kv)) ps) by (eapply Forall_impl; [|exact Hkv]; intros kv [_ H]; exact H).
destruct (w6c_pc_ents_wf sh ps es Hpv Hae Hes ltac:(lia)) as [Hn Hw].
unfold pc_image. cbn [pc_shape pc_props pc_open]. apply length_pp_image.
- destruct (pc_buf_len_open sh ps es Hpv Hae Hes) as [H _]. lia.
- exact Hn.
- eapply Forall_impl; [|exact Hw]. intros e (_ & H1 & H2). rewrite H1. lia.
Qed.

(* the image's first write range, piece by piece *)
Lemma w6c_inw1 : forall e a,
(q_F e + 0x20 <= a < q_F e + 0x158) \/ (q_R e + 0x10 <= a < q_R e + 0x38) \/ (q_R e + 0x60 <= a < q_R e + 0x120) \/
(q_R e + 0x128 <= a < q_R e + 0x140) -> rt_inw e (hi_w1 rate_himg_A) a.
Proof.
intros e a H. unfold rt_inw. cbn [hi_w1 rate_himg_A].
destruct H as [H|[H|[H|H]]].
- apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- do 2 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- do 3 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- do 4 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
Qed.

(* ======================================== a cut's geometry ======================================== *)
(* R's frame above the ceiling with the callees' stack below it, the frame for locals F and its shadow and the
   block pp below the ceiling, apart from each other *)
Definition w6c_sep (R F pp : Z) : Prop :=
alloc_ceiling + T_SEG_STK <= R /\ R + 0x1e0 <= 2 ^ 47 /\
4096 <= F /\ F + 512 <= alloc_ceiling /\ 0 <= shadow_addr F /\ shadow_addr F + 64 <= alloc_ceiling /\
(F + 512 <= shadow_addr F \/ shadow_addr F + 64 <= F) /\
4096 <= pp /\ pp + Layout.PP_SIZE <= alloc_ceiling /\
(pp + Layout.PP_SIZE <= shadow_addr F \/ shadow_addr F + 64 <= pp) /\
(pp + Layout.PP_SIZE <= F \/ F + 512 <= pp).

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

Lemma w6c_sep_of : forall cx E ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> rs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
w6c_sep (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) (q_pp (x_e rsegs cx)) /\
q_F (x_e rsegs cx) = frame_addr ly2 3 (x_pos rsegs cx).
Proof.
intros cx E ly2 S2 W2 regs2 mem2 md2 HP HC.
destruct (rs_pre_geom rsegs B cx HP) as (Hsp & HRk & HR47 & _ & HF0 & HFapp & HF32 & Happ).
pose proof HP as HP'. unfold rs_pre, rt_seg_pre in HP'.
destruct HP' as (HJ0 & _ & _ & _ & _ & HS & _ & HRs & HRstk & Hown & _ & _ & Hpp & _).
cbn [hi_cid hi_rsz rate_himg_A] in HRs, Hown.
destruct HC as (HJ & _ & _ & Hperm & _).
destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct HJ0 as (_ & Hly0 & _).
assert (HFa : q_F (x_e rsegs cx) = frame_addr ly2 3 (x_pos rsegs cx)).
{ rewrite HF0. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & E2 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & E0 & _). rewrite E2, E0. reflexivity. }
assert (Hin : In (3, x_pos rsegs cx) (frames S2)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (Hpp2 : In (q_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hpp]).
pose proof (sep_block_frame rsegs B LAWS ly2 S2 W2 mem2 md2 _ _ 3 (x_pos rsegs cx) HAR Hpp2 Hin) as Hdj.
rewrite <- HFa in Hdj.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR Hpp2) as (_ & Hp4 & Hp1 & _).
destruct Hstk as (_ & _ & Hac & Hlo & _).
destruct (rts_fbounds _ HF32 HFapp) as (B1 & B2 & B3 & B4 & B5 & _).
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hp1, Hdj by reflexivity.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. change (fs_frame_bytes 3) with 512 in Hdj.
pose proof ASAN_CEIL_range as (HC1 & _). unfold ASAN_CEIL in HC1.
pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D2.
split; [|exact HFa].
unfold w6c_sep. split; [unfold T_SEG_STK, ASTACK in *; lia|].
split; [exact HR47|].
do 5 (split; [lia|]). split; [exact Hp4|]. split; [lia|]. split; [|exact Hdj].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr, SHADOW_OFF in *. unfold Layout.PP_SIZE in *.
lia.
Qed.

(* ======================================== at D: the blocks' premises ======================================== *)
Lemma w6c_prep : forall cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD,
rs_start_M01 rsegs B cx rest ->
rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd lyD SD WD regsD memD mdD ->
w6c_ctx B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) lyD SD WD memD mdD
  (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) (x_pos rsegs cx) /\
w6c_regs B regsD (q_R (x_e rsegs cx)) (rs_cur rsegs cx rest r) (Z.of_nat (length r)) /\
w6c_cells WD memD (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) (shadow_addr (q_pp (x_e rsegs cx) + 0x4000)) /\
w6c_in WD memD (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) (rs_cur rsegs cx rest r) r /\
rtm_bytes rsegs (w_H WD) memD (q_F (x_e rsegs cx) + 0xf0) (zeros 104) /\
range_addressable (aview rsegs (w_H WD) memD) SHADOW_OFF W6C_T6 16 /\
range_addressable (aview rsegs (w_H WD) memD) SHADOW_OFF W6C_T8 16.
Proof.
intros cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD Hst HD.
destruct Hst as (HP & HFSH0 & _ & _ & HIN).
change (hi_shA rate_himg_A) with rate_A_shA in HFSH0.
destruct HD as (HB & HAT & HFSH & HPP & HE & Hsrr & Hfu & Hkd256 & Hrr).
destruct HB as (HCORE & _ & HSUF & _).
destruct (w6c_sep_of cx _ _ _ _ _ _ _ HP HCORE) as (HG & HFa).
destruct (rs_pre_geom rsegs B cx HP) as (Hsp & HRk & HR47 & _ & _ & HFapp & HF32 & Happ).
pose proof HP as HP'. unfold rs_pre, rt_seg_pre in HP'.
destruct HP' as (_ & _ & HR2 & HR3 & HR4 & HeS & HR16 & HRs & HRstk & Hown & _ & _ & _ & _ & _ & Hgl & _).
cbn [hi_cid hi_rsz hi_globs rate_himg_A] in HRs, Hown, Hgl.
unfold rs_at_cx in HAT.
pose proof HCORE as (HJD & Hr234 & _).
destruct rr as [|b r0]; [exfalso; exact (Hrr eq_refl)|].
cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst r0.
(* the context *)
split.
{ split; [exact HJD|]. split; [|exact (rs_rom_now rsegs B MT rts_segs_low cx _ _ _ _ _ _ HP HCORE)].
  unfold w6c_geo. split; [exact HR16|]. split; [exact HRstk|]. split; [rewrite <- HeS; exact HRs|].
  split; [exact HRk|]. split; [exact Hown|]. split; [exact HFa|]. split; [exact HFapp | exact HF32]. }
(* the registers *)
split.
{ unfold w6c_regs.
  split; [etransitivity; [exact (Hr234 2 ltac:(lia)) | exact HR2]|].
  split; [etransitivity; [exact (Hr234 3 ltac:(lia)) | exact HR3]|].
  split; [etransitivity; [exact (Hr234 4 ltac:(lia)) | exact HR4]|].
  split; [apply (w6c_at_reg _ _ _ _ _ 9 _ _ HAT); [w6c_unf; w6c_mem | reflexivity]|].
  split; [apply (w6c_at_reg _ _ _ _ _ 18 _ _ HAT); [w6c_unf; w6c_mem | reflexivity]|].
  split; [apply (w6c_at_reg _ _ _ _ _ 25 _ _ HAT); [w6c_unf; w6c_mem | reflexivity]|].
  split; [apply (w6c_at_reg _ _ _ _ _ 24 _ _ HAT); [w6c_unf; w6c_mem | reflexivity]|].
  split; [apply (w6c_at_reg _ _ _ _ _ 14 _ _ HAT); [w6c_unf; w6c_mem | reflexivity]|].
  apply (w6c_at_reg _ _ _ _ _ 15 _ _ HAT); [w6c_unf; w6c_mem | reflexivity]. }
(* the cells *)
split.
{ unfold w6c_cells.
  split; [apply (w6c_at_cell8 _ _ _ _ _ XR 0x138 _ HAT); w6c_unf; w6c_mem|].
  split; [apply (w6c_at_cell8 _ _ _ _ _ XR 0x108 _ HAT); w6c_unf; w6c_mem|].
  split; [apply (w6c_at_cell8 _ _ _ _ _ XR 0xe8 _ HAT); w6c_unf; w6c_mem|].
  split.
  { destruct HG as (G1 & G2 & _ & _ & _ & _ & _ & G8 & G9 & _).
    unfold shadow_addr, SHADOW_OFF, T_SEG_STK, ASTACK, Layout.PP_SIZE in *. pose proof alloc_ceiling_lt.
    pose proof (Z.div_pos (q_pp (x_e rsegs cx) + 0x4000) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (q_pp (x_e rsegs cx) + 0x4000) 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
    lia. }
  apply (w6c_at_cell8 _ _ _ _ _ XR 0x10 _ HAT); w6c_unf; w6c_mem. }
(* the input at the cursor *)
split.
{ destruct (rs_in_now rsegs B MT cx rest rs_PJ lyD SD WD regsD memD mdD HP HFSH0 HIN HCORE HFSH eq_refl)
    as (HgD & HraD & HhD).
  pose proof HIN as (Hleft & _ & _ & _ & Ham & Hsrc & Htop & Hx).
  pose proof (w6c_suffix_tl rest b r Hsrr) as HSUF'.
  destruct HSUF' as (j & Hj & Erj).
  assert (Hlr : length r = (length rest - j)%nat) by (rewrite Erj, length_skipn; reflexivity).
  assert (Hcur : rs_cur rsegs cx rest r = q_src (x_e rsegs cx) + Z.of_nat j)
    by (unfold rs_cur; rewrite Hlr; lia).
  assert (Hsb : rs_suffix rest (b :: r)) by exact Hsrr.
  destruct Hsb as (j' & Hj' & Ej').
  assert (Hl' : length (skipn j' rest) = S (length r)) by (rewrite <- Ej'; reflexivity).
  rewrite length_skipn in Hl'.
  unfold w6c_in. rewrite Hcur.
  split.
  { rewrite Erj. pose proof (w6c_src_bytes (w_H WD) memD (q_src (x_e rsegs cx)) rest j (length rest - j) HgD) as X.
    rewrite firstn_all2 in X by (rewrite length_skipn; lia). rewrite Nat.min_l in X by lia. exact X. }
  split.
  { intros x Hxx. apply HraD. rewrite Hleft. lia. }
  split.
  { intros Hn. apply (w6c_hull_sub _ (q_src (x_e rsegs cx)) (q_left (x_e rsegs cx))); [apply HhD; lia | lia | lia | lia | lia]. }
  split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
  intros a Ha. destruct (Hx a ltac:(lia)) as (D1 & D2 & _).
  split; [exact D1|].
  split; [intros X; apply D2; apply w6c_inw1; right; left; exact X|].
  split; [intros X; apply D2; apply w6c_inw1; right; right; left; exact X|].
  split; [intros X; apply D2; apply w6c_inw1; right; right; right; exact X|].
  intros X; apply D2; apply w6c_inw1; left; exact X. }
(* e's zeros *)
split; [exact HE|].
(* the two tables' shadow *)
assert (HT : forall t, In (t, 16) rate_A_globs -> 0 <= t < 0x30000 ->
  range_addressable (aview rsegs (w_H WD) memD) SHADOW_OFF t 16).
{ intros t Ht Ht64. assert (Hg0 : range_addressable (aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx)) SHADOW_OFF t 16).
  { rewrite Forall_forall in Hgl. exact (Hgl (t, 16) Ht). }
  intros x Hxx.
  rewrite (rs_core_kept rsegs B MT cx _ _ _ _ _ _ HP HCORE (shadow_of_addr SHADOW_OFF x)); [exact (Hg0 x Hxx)|].
  apply (rs_wr_shadow rsegs B cx x HP HFSH0).
  - unfold kHighMemEnd. lia.
  - intros y Hy. apply Hg0. lia. }
split; (apply HT; [unfold rate_A_globs; w6c_mem | unfold W6C_T6, W6C_T8; lia]).
Qed.

(* ======================================== at J: the cut ======================================== *)
Lemma w6c_to_J : forall cx POST rest i k sh np ps cnt es rr r kd lyD SD WD regsD memD mdD regsJ memJ mdJ ed r',
rs_start_M01 rsegs B cx rest -> rs_from_J rsegs B MT cx POST rest i k -> (length ps = i)%nat -> (length es = k)%nat ->
rs_cut_D rsegs B MT cx sh np ps cnt es rest rr r kd lyD SD WD regsD memD mdD ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) lyD SD WD memJ mdJ (x_k rsegs cx) ->
same_io mdD mdJ ->
(forall q, In q w6c_keep -> getr regsJ q = getr regsD q) ->
getr regsJ 22 = w64 (shadow_addr (q_pp (x_e rsegs cx) + 0x4000)) ->
getr regsJ 24 = w64 (Z.of_nat (length r')) -> getr regsJ 25 = w64 (rs_cur rsegs cx rest r') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - ESTACK <= a < q_R (x_e rsegs cx)) ->
 ~ (q_F (x_e rsegs cx) + 0xf0 <= a < q_F (x_e rsegs cx) + 0x158) ->
 aview rsegs (w_H WD) memJ a = aview rsegs (w_H WD) memD a) ->
rtm_bytes rsegs (w_H WD) memJ (q_F (x_e rsegs cx) + 0xf0) (ent_mem ed) ->
(ed, r') = ent_build rr -> rs_suffix rest r' ->
SRr rsegs WD (cfg_at rsegs RS_J regsJ memJ mdJ) POST.
Proof.
intros cx POST rest i k sh np ps cnt es rr r kd lyD SD WD regsD memD mdD regsJ memJ mdJ ed r'
  Hst HJ Hlp Hle HD HJJ HioJ HKR J22 J24 J25 HMJ HEJ Hed HsJ.
destruct Hst as (HP & _).
destruct HD as (HB & HAT & HFSH & HPP & _).
pose proof HB as HB0.
destruct HB as (HCORE & HIN & _ & HSrr & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hesw & Hesl & _).
destruct (w6c_sep_of cx _ _ _ _ _ _ _ HP HCORE) as (HG & HFa).
destruct (rs_pre_geom rsegs B cx HP) as (Hsp & HRk & _).
pose proof (w6c_pp_len sh ps es Hwf Hesw Hesl) as Hppl.
pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof alloc_ceiling_lt as Hc47.
(* the journal-and-frame part *)
assert (HCJ : rs_core rsegs B MT cx (rs_E1 rsegs cx) lyD SD WD regsJ memJ mdJ).
{ destruct HCORE as (_ & Hr234 & Hf & Hpm & Hio & Hmo & Hm).
  split; [exact HJJ|].
  split.
  { intros q Hq. rewrite <- (Hr234 q Hq). apply (w6c_keepZ_bv regsD regsJ HKR).
    destruct Hq as [->|[->| ->]]; unfold w6c_keepZ; w6c_mem. }
  split; [exact Hf|]. split; [exact Hpm|]. split; [eapply same_io_trans; [exact Hio | exact HioJ]|]. split; [exact Hmo|].
  intros a Ha Hs HE1. rewrite <- (Hm a Ha Hs HE1). apply HMJ; [exact Ha | | ].
  - rewrite Hsp in Hs. unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - intros X. apply HE1. left. apply w6c_inw1. left. lia. }
(* the cells of the real frame, kept *)
assert (HRK : forall o ii, 0 <= o <= 0x178 -> 0 <= ii < 8 ->
  aview rsegs (w_H WD) memJ (q_R (x_e rsegs cx) + o + ii) = aview rsegs (w_H WD) memD (q_R (x_e rsegs cx) + o + ii)).
{ intros o ii Ho Hii. apply HMJ; unfold T_SEG_STK, ASTACK, ESTACK in *; lia. }
unfold rs_from_J in HJ.
apply (HJ lyD SD WD regsJ memJ mdJ sh np ps cnt es rr r' ed Hlp Hle).
split.
{ (* rs_pod_base at J *)
  destruct HB0 as (_ & H1 & _ & H3). exact (conj HCJ (conj H1 (conj HsJ H3))). }
split.
{ unfold rs_at_cx in HAT |- *.
  assert (D26 : getr regsD (Z_to_bv 5 26) = w64 (-0x4001)).
  { apply (w6c_at_get _ _ _ _ _ (LReg 26) _ HAT). w6c_unf. w6c_mem. }
  assert (HATc : rs_at rsegs (w_H WD) memD regsD (x_e rsegs cx) (rs_L_Dc rsegs cx sh np ps cnt es)).
  { unfold rs_at in HAT |- *. unfold rs_L_D in HAT. apply Forall_app in HAT as [X _]. exact X. }
  assert (HATJ : rs_at rsegs (w_H WD) memJ regsJ (x_e rsegs cx) (rs_L_Dc rsegs cx sh np ps cnt es)).
  { apply (w6c_keeps_L (w_H WD) memD (w_H WD) memJ regsD regsJ _ _); [vm_compute; reflexivity | | exact HRK | exact HATc].
    exact (w6c_keepZ_bv regsD regsJ HKR). }
  unfold rs_at in HATJ |- *. apply Forall_app. split; [exact HATJ|].
  repeat apply Forall_cons; cbn [fst snd rt_at]; try apply Forall_nil.
  - exact J22.
  - exact J25.
  - exact J24.
  - rewrite (w6c_keepZ_bv regsD regsJ HKR 26 ltac:(unfold w6c_keepZ; w6c_mem)). exact D26. }
split.
{ unfold rs_fsh_at in *. apply (rtm_fsh_kept rsegs (w_H WD) memD (w_H WD) memJ _ _ HFSH).
  intros ii Hii. change (Z.of_nat (length rs_PJ)) with 56 in Hii.
  apply HMJ; unfold T_SEG_STK, ASTACK, ESTACK in *; lia. }
split.
{ unfold rs_pp_at in *. apply (rtm_bytes_kept rsegs (w_H WD) memD (w_H WD) memJ _ _ HPP).
  intros x Hx. rewrite Hppl in Hx.
  apply HMJ; unfold T_SEG_STK, ASTACK, ESTACK, Layout.PP_SIZE in *; lia. }
split; [exact HEJ|].
split; [exact Hed|].
pose proof (ent_build_wf rr) as X. rewrite <- Hed in X. exact X.
Qed.

(* ======================================== the three cases ======================================== *)
Section h.
Hypothesis H6 : w6c_h6_stmt B.
Hypothesis H7 : w6c_h7_stmt B.
Hypothesis H8 : w6c_h8_stmt B.
Hypothesis HCPY : w6c_tail_cpy_stmt B.
Hypothesis HSET : w6c_tail_set_stmt B.

(* the memory a head keeps, then the one its tail keeps *)
Lemma w6c_mem_chain : forall (W : world rsegs) memD memT memJ R F,
(forall a, 0 <= a < 2 ^ 64 -> ~ w6c_hdr_wr F a -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memD a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0xf0 <= a < F + 0x158) ->
 aview rsegs (w_H W) memJ a = aview rsegs (w_H W) memT a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0xf0 <= a < F + 0x158) ->
aview rsegs (w_H W) memJ a = aview rsegs (w_H W) memD a.
Proof.
intros W memD memT memJ R F HmT HmJ a Ha H1 H2. rewrite (HmJ a Ha H1 H2). apply HmT; [exact Ha|].
unfold w6c_hdr_wr. lia.
Qed.
(* the frame's shadow at the head's end *)
Lemma w6c_fsh_T : forall (W : world rsegs) memD memT R F pp,
w6c_sep R F pp -> rt_fsh rsegs (w_H W) memD F rs_PJ ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w6c_hdr_wr F a -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memD a) ->
rt_fsh rsegs (w_H W) memT F rs_PJ.
Proof.
intros W memD memT R F pp HG HF HmT. pose proof alloc_ceiling_lt as Hc.
destruct HG as (_ & _ & G3 & G4 & G5 & G6 & G7 & _).
apply (rtm_fsh_kept rsegs (w_H W) memD (w_H W) memT _ _ HF).
intros ii Hii. change (Z.of_nat (length rs_PJ)) with 56 in Hii.
apply HmT; [lia | unfold w6c_hdr_wr; lia].
Qed.

Lemma w6c_case6 : forall cx POST rest i k kd, kd mod 10 = 6 ->
rs_start_M01 rsegs B cx rest -> rs_from_J rsegs B MT cx POST rest i k -> rs_from_D rsegs B MT cx POST rest i k kd.
Proof using H6 HCPY.
intros cx POST rest i k kd Hkd Hst HJ. unfold rs_from_D.
intros lyD SD WD regsD memD mdD sh np ps cnt es rr r Hlp Hle HD.
destruct (w6c_prep cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD Hst HD)
  as (HCTX & HREGS & HCELLS & HIN & HZ & HT6 & _).
pose proof Hst as (HP & _).
pose proof HD as (HB & _ & HFSH & _ & _ & Hsrr & Hfu & _ & Hrr).
pose proof HB as (HCORE & _ & HSUF & _).
destruct (w6c_sep_of cx _ _ _ _ _ _ _ HP HCORE) as (HG & _).
pose proof HCTX as (HJD & HGEO & _).
pose proof HGEO as (_ & _ & _ & _ & _ & _ & HFapp & _).
destruct rr as [|b r0]; [exfalso; exact (Hrr eq_refl)|].
cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd r0.
replace (rs_pc_D (bv_unsigned b)) with W6C_D6 by (unfold rs_pc_D; rewrite Hkd; reflexivity).
pose proof HREGS as (D2 & D3 & D4 & D9 & D18 & D25 & D24 & D14 & D15).
eapply SRr_bind; [exact (H6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsD _ _ _ _ _ r HCTX HREGS HCELLS HIN HZ HT6)|].
intros WT cT _ HPT. destruct HPT as (regsT & memT & mdT & EW & -> & HJT & HioT & HkT & HmT & HQ). subst WT.
cbv zeta in HQ. destruct HQ as (T1 & T10 & T11 & T12 & T22 & T24 & T25 & Vty & Vsz).
pose proof (w6c_sz6_rng (w6c_ty6 (fst (fuzz_u8 r)))) as Hsz.
set (sz := w6c_sz6 (w6c_ty6 (fst (fuzz_u8 r)))) in *.
set (ty := w6c_ty6 (fst (fuzz_u8 r))) in *.
assert (Er1 : snd (fuzz_u8 r) = skipn 1 r) by apply w6c_u8_rest.
rewrite Er1 in *.
assert (Hl1 : Z.of_nat (length (skipn 1 r)) = Z.of_nat (length r) - Z.of_nat (Nat.min 1 (length r)))
  by (rewrite length_skipn; lia).
destruct (w6c_src_ok WD memD memT _ _ (rs_cur rsegs cx rest r) r 1 (Z.to_nat sz) ty sz HIN HFapp HmT Vty Vsz)
  as (Sb & Sra & Shl & Sam & S0 & S63 & Sdis).
set (bs := firstn (Z.to_nat sz) (skipn 1 r)) in *.
assert (Hbs : Z.of_nat (length bs) = Z.min sz (Z.of_nat (length (skipn 1 r)))) by (subst bs; rewrite length_firstn; lia).
assert (Esrc : rs_cur rsegs cx rest r + Z.of_nat (length r) - Z.of_nat (length (skipn 1 r)) =
  rs_cur rsegs cx rest r + Z.of_nat (Nat.min 1 (length r))) by lia.
rewrite Esrc in T11, T25.
eapply SRr_bind.
{ apply (HCPY (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) lyD SD WD memT mdT regsT
    (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) (x_pos rsegs cx) ty sz
    (rs_cur rsegs cx rest r + Z.of_nat (Nat.min 1 (length r))) bs
    (rs_cur rsegs cx rest r + Z.of_nat (Nat.min 1 (length r)) + Z.min sz (Z.of_nat (length (skipn 1 r))))
    (Z.of_nat (length (skipn 1 r)) - Z.min sz (Z.of_nat (length (skipn 1 r))))
    (shadow_addr (q_pp (x_e rsegs cx) + 0x4000)) HJT HGEO T1).
  - w6c_kept HkT. exact D2.
  - w6c_kept HkT. exact D3.
  - w6c_kept HkT. exact D4.
  - exact T10.
  - exact T11.
  - rewrite Hbs. exact T12.
  - exact T22.
  - exact T24.
  - exact T25.
  - subst bs. rewrite length_firstn. lia.
  - lia.
  - apply (w6c_hdr_bytes (w_H WD) memD (w_H WD) memT _ ty sz HZ Vty Vsz).
    intros a Ha. destruct HG as (_ & _ & G3 & G4 & _). pose proof alloc_ceiling_lt.
    apply HmT; [lia | unfold w6c_hdr_wr; lia].
  - exact Sb.
  - exact Sra.
  - exact Shl.
  - exact Sam.
  - exact S0.
  - exact S63.
  - exact Sdis.
  - exact (w6c_fsh_T WD memD memT _ _ _ HG HFSH HmT). }
intros WJ cJ _ HPJ. destruct HPJ as (regsJ & memJ & mdJ & EW & -> & HJJ & HioJ & HkJ & J22 & J24 & J25 & HmJ & HEJ).
subst WJ.
eapply (w6c_to_J cx POST rest i k sh np ps cnt es (b :: r) r (bv_unsigned b) lyD SD WD regsD memD mdD regsJ memJ mdJ
  _ (skipn (Z.to_nat sz) (skipn 1 r)) Hst HJ Hlp Hle HD HJJ).
- eapply same_io_trans; [exact HioT | exact HioJ].
- intros q Hq. rewrite (HkJ q Hq). destruct (w6c_keep_clob q Hq) as (Hq0 & Hq1 & _). exact (HkT q Hq0 Hq1).
- exact J22.
- rewrite J24. f_equal. rewrite !length_skipn. lia.
- rewrite J25. f_equal. unfold rs_cur. rewrite !length_skipn. lia.
- exact (w6c_mem_chain WD memD memT memJ _ _ HmT HmJ).
- exact HEJ.
- rewrite (w6c_ent6 b r Hkd). rewrite Er1. reflexivity.
- apply w6c_suffix_skip. apply w6c_suffix_skip. exact HSUF.
Qed.

Lemma w6c_case7 : forall cx POST rest i k kd, kd mod 10 = 7 ->
rs_start_M01 rsegs B cx rest -> rs_from_J rsegs B MT cx POST rest i k -> rs_from_D rsegs B MT cx POST rest i k kd.
Proof using H7 HCPY.
intros cx POST rest i k kd Hkd Hst HJ. unfold rs_from_D.
intros lyD SD WD regsD memD mdD sh np ps cnt es rr r Hlp Hle HD.
destruct (w6c_prep cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD Hst HD)
  as (HCTX & HREGS & HCELLS & HIN & HZ & _ & _).
pose proof Hst as (HP & _).
pose proof HD as (HB & _ & HFSH & _ & _ & Hsrr & Hfu & _ & Hrr).
pose proof HB as (HCORE & _ & HSUF & _).
destruct (w6c_sep_of cx _ _ _ _ _ _ _ HP HCORE) as (HG & _).
pose proof HCTX as (HJD & HGEO & _).
pose proof HGEO as (_ & _ & _ & _ & _ & _ & HFapp & _).
destruct rr as [|b r0]; [exfalso; exact (Hrr eq_refl)|].
cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd r0.
replace (rs_pc_D (bv_unsigned b)) with W6C_D7 by (unfold rs_pc_D; rewrite Hkd; reflexivity).
pose proof HREGS as (D2 & D3 & D4 & D9 & D18 & D25 & D24 & D14 & D15).
eapply SRr_bind; [exact (H7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsD _ _ _ _ _ r HCTX HREGS HCELLS HIN HZ)|].
intros WT cT _ HPT. destruct HPT as (regsT & memT & mdT & EW & -> & HJT & HioT & HkT & HmT & HQ). subst WT.
cbv zeta in HQ. destruct HQ as (T1 & T10 & T11 & T12 & T22 & T24 & T25 & Vty & Vsz).
assert (Er2 : snd (fuzz_u8 (snd (fuzz_u8 r))) = skipn 2 r)
  by (rewrite !w6c_u8_rest, skipn_skipn; reflexivity).
assert (Hsz : 0 <= fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12 < 12) by (apply Z.mod_pos_bound; lia).
set (sz := fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12) in *.
set (ty := fst (fuzz_u8 r) mod 21) in *.
rewrite Er2 in *.
destruct (w6c_src_ok WD memD memT _ _ (rs_cur rsegs cx rest r) r 2 (Z.to_nat sz) ty sz HIN HFapp HmT Vty Vsz)
  as (Sb & Sra & Shl & Sam & S0 & S63 & Sdis).
set (bs := firstn (Z.to_nat sz) (skipn 2 r)) in *.
assert (Hbs : Z.of_nat (length bs) = Z.min sz (Z.of_nat (length (skipn 2 r)))) by (subst bs; rewrite length_firstn; lia).
assert (Esrc : rs_cur rsegs cx rest r + Z.of_nat (length r) - Z.of_nat (length (skipn 2 r)) =
  rs_cur rsegs cx rest r + Z.of_nat (Nat.min 2 (length r))) by (rewrite length_skipn; lia).
rewrite Esrc in T11, T25.
eapply SRr_bind.
{ apply (HCPY (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) lyD SD WD memT mdT regsT
    (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) (x_pos rsegs cx) ty sz
    (rs_cur rsegs cx rest r + Z.of_nat (Nat.min 2 (length r))) bs
    (rs_cur rsegs cx rest r + Z.of_nat (Nat.min 2 (length r)) + Z.min sz (Z.of_nat (length (skipn 2 r))))
    (Z.of_nat (length (skipn 2 r)) - Z.min sz (Z.of_nat (length (skipn 2 r))))
    (shadow_addr (q_pp (x_e rsegs cx) + 0x4000)) HJT HGEO T1).
  - w6c_kept HkT. exact D2.
  - w6c_kept HkT. exact D3.
  - w6c_kept HkT. exact D4.
  - exact T10.
  - exact T11.
  - rewrite Hbs. exact T12.
  - exact T22.
  - exact T24.
  - exact T25.
  - subst bs. rewrite length_firstn. lia.
  - lia.
  - apply (w6c_hdr_bytes (w_H WD) memD (w_H WD) memT _ ty sz HZ Vty Vsz).
    intros a Ha. destruct HG as (_ & _ & G3 & G4 & _). pose proof alloc_ceiling_lt.
    apply HmT; [lia | unfold w6c_hdr_wr; lia].
  - exact Sb.
  - exact Sra.
  - exact Shl.
  - exact Sam.
  - exact S0.
  - exact S63.
  - exact Sdis.
  - exact (w6c_fsh_T WD memD memT _ _ _ HG HFSH HmT). }
intros WJ cJ _ HPJ. destruct HPJ as (regsJ & memJ & mdJ & EW & -> & HJJ & HioJ & HkJ & J22 & J24 & J25 & HmJ & HEJ).
subst WJ.
eapply (w6c_to_J cx POST rest i k sh np ps cnt es (b :: r) r (bv_unsigned b) lyD SD WD regsD memD mdD regsJ memJ mdJ
  _ (skipn (Z.to_nat sz) (skipn 2 r)) Hst HJ Hlp Hle HD HJJ).
- eapply same_io_trans; [exact HioT | exact HioJ].
- intros q Hq. rewrite (HkJ q Hq). destruct (w6c_keep_clob q Hq) as (Hq0 & Hq1 & _). exact (HkT q Hq0 Hq1).
- exact J22.
- rewrite J24. f_equal. rewrite !length_skipn. lia.
- rewrite J25. f_equal. unfold rs_cur. rewrite !length_skipn. lia.
- exact (w6c_mem_chain WD memD memT memJ _ _ HmT HmJ).
- exact HEJ.
- rewrite (w6c_ent7 b r Hkd). rewrite Er2. reflexivity.
- apply w6c_suffix_skip. apply w6c_suffix_skip. exact HSUF.
Qed.

Lemma w6c_case8 : forall cx POST rest i k kd, kd mod 10 = 8 ->
rs_start_M01 rsegs B cx rest -> rs_from_J rsegs B MT cx POST rest i k -> rs_from_D rsegs B MT cx POST rest i k kd.
Proof using H8 HSET.
intros cx POST rest i k kd Hkd Hst HJ. unfold rs_from_D.
intros lyD SD WD regsD memD mdD sh np ps cnt es rr r Hlp Hle HD.
destruct (w6c_prep cx rest sh np ps cnt es rr r kd lyD SD WD regsD memD mdD Hst HD)
  as (HCTX & HREGS & HCELLS & HIN & HZ & _ & HT8).
pose proof Hst as (HP & _).
pose proof HD as (HB & _ & HFSH & _ & _ & Hsrr & Hfu & _ & Hrr).
pose proof HB as (HCORE & _ & HSUF & _).
destruct (w6c_sep_of cx _ _ _ _ _ _ _ HP HCORE) as (HG & _).
pose proof HCTX as (HJD & HGEO & _).
destruct rr as [|b r0]; [exfalso; exact (Hrr eq_refl)|].
cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd r0.
replace (rs_pc_D (bv_unsigned b)) with W6C_D8 by (unfold rs_pc_D; rewrite Hkd; reflexivity).
pose proof HREGS as (D2 & D3 & D4 & D9 & D18 & D25 & D24 & D14 & D15).
pose proof HCELLS as (_ & _ & Ce8 & Hvb & _).
eapply SRr_bind; [exact (H8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regsD _ _ _ _ _ r HCTX HREGS HCELLS HIN HZ HT8)|].
intros WT cT _ HPT. destruct HPT as (regsT & memT & mdT & EW & -> & HJT & HioT & HkT & HmT & HQ). subst WT.
cbv zeta in HQ. destruct HQ as (T1 & T10 & T11 & T12 & T22 & T25 & Vty & Vsz).
pose proof (w6c_sz8_rng (w6c_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r))) as Hsz.
pose proof (w6c_sz8_len (w6c_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r))) as Hlr'.
set (r' := snd (w6c_sz8 (w6c_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r)))) in *.
set (sz := fst (w6c_sz8 (w6c_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r)))) in *.
set (ty := w6c_ty8 (fst (fuzz_u8 r))) in *.
eapply SRr_bind.
{ apply (HSET (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) lyD SD WD memT mdT regsT
    (q_R (x_e rsegs cx)) (q_F (x_e rsegs cx)) (x_pos rsegs cx) ty sz
    (rs_cur rsegs cx rest r + Z.of_nat (length r) - Z.of_nat (length r')) (Z.of_nat (length r'))
    (shadow_addr (q_pp (x_e rsegs cx) + 0x4000)) HJT HGEO T1).
  - w6c_kept HkT. exact D2.
  - w6c_kept HkT. exact D3.
  - w6c_kept HkT. exact D4.
  - w6c_kept HkT. exact D9.
  - exact T10.
  - exact T11.
  - exact T12.
  - exact T22.
  - exact T25.
  - lia.
  - exact Hvb.
  - apply (w6c_hdr_bytes (w_H WD) memD (w_H WD) memT _ ty sz HZ Vty Vsz).
    intros a Ha. destruct HG as (_ & _ & G3 & G4 & _). pose proof alloc_ceiling_lt.
    apply HmT; [lia | unfold w6c_hdr_wr; lia].
  - exact (w6c_fsh_T WD memD memT _ _ _ HG HFSH HmT).
  - apply (w6c_val_kept (w_H WD) memD (w_H WD) memT _ 8 _ Ce8).
    intros ii Hii. change (Z.of_nat 8) with 8 in Hii. destruct HG as (G1 & G2 & G3 & G4 & _). pose proof alloc_ceiling_lt.
    apply HmT; [unfold T_SEG_STK, ASTACK in *; lia | unfold w6c_hdr_wr, T_SEG_STK, ASTACK in *; lia]. }
intros WJ cJ _ HPJ. destruct HPJ as (regsJ & memJ & mdJ & EW & -> & HJJ & HioJ & HkJ & J22 & J24 & J25 & HmJ & HEJ).
subst WJ.
eapply (w6c_to_J cx POST rest i k sh np ps cnt es (b :: r) r (bv_unsigned b) lyD SD WD regsD memD mdD regsJ memJ mdJ
  _ r' Hst HJ Hlp Hle HD HJJ).
- eapply same_io_trans; [exact HioT | exact HioJ].
- intros q Hq. rewrite (HkJ q Hq). destruct (w6c_keep_clob q Hq) as (Hq0 & _ & Hq2). exact (HkT q Hq0 Hq2).
- exact J22.
- exact J24.
- rewrite J25. f_equal. unfold rs_cur. lia.
- exact (w6c_mem_chain WD memD memT memJ _ _ HmT HmJ).
- exact HEJ.
- rewrite (w6c_ent8 b r Hkd). reflexivity.
- apply w6c_sz8_suf. rewrite w6c_u8_rest. apply w6c_suffix_skip. exact HSUF.
Qed.

Theorem w6c_piece_h : rs_piece_W6c_stmt rsegs B MT.
Proof using H6 H7 H8 HCPY HSET.
intros cx POST rest i k kd Hst Hin HJ.
cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]].
- exact (w6c_case6 cx POST rest i k kd (eq_sym E) Hst HJ).
- exact (w6c_case7 cx POST rest i k kd (eq_sym E) Hst HJ).
- exact (w6c_case8 cx POST rest i k kd (eq_sym E) Hst HJ).
Qed.
End h.

(* ======================================== the piece ========================================
   The three heads (lib/A/RtPgW6c6.v, RtPgW6c7.v, RtPgW6c8.v) and the two tails (lib/A/RtPgW6cTail.v) proved; the
   two intrinsics' contracts (the kernel's aintrin_realizes at __asan_memcpy 0x51860 and __asan_memset 0x51cfc) are
   the piece's premises. *)
Theorem w6c_piece : aintrin_realizes rsegs B OCpy W6C_CPY -> aintrin_realizes rsegs B OSet W6C_SET ->
rs_piece_W6c_stmt rsegs B MT.
Proof.
intros AMEMCPY AMEMSET.
exact (w6c_piece_h (RtPgW6c6.w6c_h6 B) (RtPgW6c7.w6c_h7 B) (RtPgW6c8.w6c_h8 B) (w6c_tail_cpy B AMEMCPY)
  (w6c_tail_set B AMEMSET)).
Qed.
End d.
End b.

Print Assumptions w6c_piece_h.
Print Assumptions w6c_piece.
