(* The caller's struct diginet_cmd at out, in the image-A walks of the encoders that write it (lib/A/Prog/CPgEncC.v
   cenc_out / cenc_res / cenc_wr). Generic in the atom m of the register that holds out at entry (a1 = atom 11,
   a3 = atom 13) and in the length n of the bytes the encoder writes at out[0..n) (3; fader 5).
   - Entry (ceo_entry): CPgWalk's base regions cw_regs 16, no region for out, and out's atom fact ceo_fact m (out lies
     in [4096, 0x7fffff800000]); the walk adds out's shadow entry mkSHE m 0 32 (CPgWalk.cw_shent_cdst). With them the
     engine decides `beqz` of out and every instrumented check of out.
   - A failing path writes nothing to out. So out has no region while a path may still fail: KE's zone is the save
     area [sp - 16, sp), and at `ret` ceo_res_fail gives cenc_res with out unchanged.
   - On the success path, once the last failing branch is passed, ceo_add3 puts the three write windows ceo_regs m n
     (out[0..n), out[24..26), out[28..32), no chunk) on top of the state's regions; ceo_disj proves them apart from
     the regions there, ceo_KE_widen widens KE's zone to ceo_zone, ceo_awr / ceo_kwr are the run's write-range and
     zone tactics. At `ret`, ceo_chunks reads the windows' chunks, ceo_chunk1 / ceo_chunk4 turn each chunk into the
     byte it holds, and ceo_res_ok gives garr8 out (cmd_outZ before o) from those bytes and KE for out[n..24) and
     out[26..28).
   - Leaf memory clause: ceo_eimg (no byte of out is a byte of the image) and the zone cover for CPgWalk.cw_kept. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
(* the spec first: DgnLib's st_ok (a running status) must not hide the engine's st_ok *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ shapes ================================ *)
(* a write window [lo, hi) of out, on the atom m that holds out; it holds no chunk when it is made *)
Definition ceo_win (m : nat) (lo hi : Z) : YP09.region := YP09.mkRegion (Some m) lo hi lo hi [].
(* the three windows a successful encoder writes: out[0..n), the len and display bytes out[24..26), the key
   out[28..32) *)
Definition ceo_regs (m : nat) (n : Z) : smem := [ceo_win m 0 n; ceo_win m 24 26; ceo_win m 28 32].
(* out's atom fact: cdst_ok puts out in a heap block or a live side-stack frame, so 4096 <= out < alloc_ceiling *)
Definition ceo_fact (m : nat) : nat * afact := (m, mkAF 4096 0x7fffff800000 0).
(* the zone of a success path's writes: the save area and the three windows *)
Definition ceo_zone (sp out n a : Z) : Prop :=
sp - 16 <= a < sp \/ out <= a < out + n \/ out + 24 <= a < out + 26 \/ out + 28 <= a < out + 32.

(* ================================ list and byte facts ================================ *)
Lemma ceo_nth_map_u8 : forall bs j, (j < length bs)%nat -> nth j (map u8 bs) 0 = u8 (nth j bs 0).
Proof.
induction bs as [|b bs IH]; intros j Hj; cbn [length] in Hj; [lia|].
destruct j as [|j]; cbn [map nth]; [reflexivity | apply IH; lia].
Qed.
Lemma ceo_nth_skipn : forall (l : list Z) n i, nth i (skipn n l) 0 = nth (n + i) l 0.
Proof.
induction l as [|x l IH]; intros n i.
- destruct n; cbn [skipn]; rewrite !nth_overflow by (cbn [length]; lia); reflexivity.
- destruct n as [|n]; cbn [skipn]; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma ceo_nth_firstn : forall (l : list Z) n i, (i < n)%nat -> nth i (firstn n l) 0 = nth i l 0.
Proof.
induction l as [|x l IH]; intros n i Hi; (destruct n as [|n]; [lia|]); cbn [firstn]; [reflexivity|].
destruct i as [|i]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma ceo_bv8 : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H.
Qed.
(* one byte of a val_mem, from the byte the memory holds *)
Lemma ceo_val1 : forall (m : word -> option byte) a x v,
mbyte tfibsegs m a = Some (Z_to_bv 8 x) -> x mod 256 = v mod 256 -> val_mem tfibsegs m a 1 v.
Proof.
intros m a x v Hm Hx k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Hm. f_equal.
apply ceo_bv8. unfold YO0f.le_byte. cbn [Z.of_nat]. change (2 ^ (8 * 1)) with 256. change (8 * 0) with 0.
rewrite Z.shiftr_0_r, !Z.mod_mod by lia. exact Hx.
Qed.
Lemma ceo_garr8_kept : forall H (memc mem2 : word -> option byte) out l,
garr8 tfibsegs (mrestrict H memc) out l ->
(forall a, out <= a < out + Z.of_nat (length l) -> aview tfibsegs H mem2 a = aview tfibsegs H memc a) ->
garr8 tfibsegs (mrestrict H mem2) out l.
Proof.
intros H memc mem2 out l HG HK j Hj. destruct (HG j Hj) as (Hv & Hr). split; [|exact Hr].
apply (cw_val_mem_kept H H memc mem2 _ 1 _); [intros x Hx; cbn [Z.of_nat] in Hx; apply HK; lia | exact Hv].
Qed.
(* the byte a 1-byte chunk holds, from its value modulo 256 *)
Lemma ceo_chunk1 : forall E (m : word -> option byte) base off e v,
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 e)) -> U E e mod 256 = v mod 256 ->
mbyte tfibsegs m (base + off) = Some (Z_to_bv 8 v).
Proof.
intros E m base off e v HC Hv. destruct (HC 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. rewrite Z.add_0_r in Hb2. rewrite Hb2. injection Hb1 as <-. f_equal.
unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r. apply ceo_bv8. exact Hv.
Qed.
(* the four bytes a 4-byte chunk holds, from its value modulo 2 ^ 32 *)
Lemma ceo_chunk4 : forall E (m : word -> option byte) base off e key,
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 4 e)) -> U E e mod 2 ^ 32 = key mod 2 ^ 32 ->
forall j, 0 <= j < 4 -> mbyte tfibsegs m (base + off + j) = Some (Z_to_bv 8 (key / 2 ^ (8 * j))).
Proof.
intros E m base off e key HC Hv j Hj. destruct (HC j ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. rewrite Hb2. injection Hb1 as <-. f_equal.
unfold byte_of_word. fold (U E e). apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). rewrite <- (Z.shiftr_div_pow2 key) by lia.
assert (Hb : forall k, 0 <= k < 32 -> Z.testbit (U E e) k = Z.testbit key k).
{ intros k Hk. rewrite <- (Z.mod_pow2_bits_low (U E e) 32 k) by lia.
  rewrite <- (Z.mod_pow2_bits_low key 32 k) by lia. rewrite Hv. reflexivity. }
apply Z.bits_inj'. intros i Hi. destruct (Z.ltb_spec i 8).
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. apply Hb. lia.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
(* U of an atom plus a constant, modulo 256 *)
Lemma ceo_U_off : forall E n x c, ew E n = Z_to_bv 64 x -> U E (SOff n c) mod 256 = (x + c) mod 256.
Proof.
intros E n x c H. rewrite U_SOff, H, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
assert (D : forall y, (y mod 2 ^ 64) mod 256 = y mod 256).
{ intros y. apply Z.mod_mod_divide. exists (2 ^ 56). reflexivity. }
rewrite D, (Z.add_mod (x mod 2 ^ 64) c 256), (Z.add_mod x c 256) by lia. rewrite D. reflexivity.
Qed.

(* ================================ the 32 bytes of a command ================================ *)
(* garr8 out (cmd_outZ before (Some (bs, key, disp))): bytes [0, n) and 24, 25, 28..31 from the memory, the
   others kept from the call's start *)
Lemma ceo_res_ok : forall H (memc mem2 : word -> option byte) out before bs key disp,
length before = 32%nat -> (length bs <= 24)%nat ->
garr8 tfibsegs (mrestrict H memc) out before ->
(forall j, (j < length bs)%nat -> mbyte tfibsegs (mrestrict H mem2) (out + Z.of_nat j) = Some (Z_to_bv 8 (nth j bs 0))) ->
mbyte tfibsegs (mrestrict H mem2) (out + 24) = Some (Z_to_bv 8 (Z.of_nat (length bs))) ->
mbyte tfibsegs (mrestrict H mem2) (out + 25) = Some (Z_to_bv 8 disp) ->
(forall j, 0 <= j < 4 -> mbyte tfibsegs (mrestrict H mem2) (out + 28 + j) = Some (Z_to_bv 8 (key / 2 ^ (8 * j)))) ->
(forall a, out + Z.of_nat (length bs) <= a < out + 24 \/ out + 26 <= a < out + 28 ->
  aview tfibsegs H mem2 a = aview tfibsegs H memc a) ->
garr8 tfibsegs (mrestrict H mem2) out (cmd_outZ before (Some (bs, key, disp))).
Proof.
intros H memc mem2 out before bs key disp Hlb Hls HG Hbs H24 H25 Hk HK j Hj.
assert (Hlen : length (cmd_outZ before (Some (bs, key, disp))) = 32%nat).
{ unfold cmd_outZ, le4Z. rewrite !length_app, length_map, length_skipn, length_firstn, length_firstn, length_skipn, Hlb.
  cbn [length]. lia. }
rewrite Hlen in Hj.
assert (KB : forall i, (i < 32)%nat -> (length bs <= i)%nat -> (i < 24 \/ 26 <= i < 28)%nat ->
  val_mem tfibsegs (mrestrict H mem2) (out + Z.of_nat i) 1 (nth i before 0) /\ 0 <= nth i before 0 < 256).
{ intros i Hi Hn Hr. destruct (HG i ltac:(lia)) as (Hv & Hb). split; [|exact Hb].
  apply (cw_val_mem_kept H H memc mem2 _ 1 _); [intros x Hx; cbn [Z.of_nat] in Hx; apply HK; lia | exact Hv]. }
unfold cmd_outZ.
destruct (Nat.lt_ge_cases j (length bs)) as [J1|J1].
{ rewrite app_nth1 by (rewrite length_map; exact J1). rewrite (ceo_nth_map_u8 bs j J1).
  split; [| unfold u8; apply Z.mod_pos_bound; lia].
  apply (ceo_val1 _ _ (nth j bs 0)); [exact (Hbs j J1) | unfold u8; rewrite Z.mod_mod by lia; reflexivity]. }
rewrite app_nth2 by (rewrite length_map; exact J1). rewrite length_map.
destruct (Nat.lt_ge_cases j 24) as [J2|J2].
{ rewrite app_nth1 by (rewrite length_skipn, length_firstn, Hlb; lia).
  rewrite ceo_nth_skipn, ceo_nth_firstn by lia. replace (length bs + (j - length bs))%nat with j by lia.
  apply KB; lia. }
rewrite app_nth2 by (rewrite length_skipn, length_firstn, Hlb; lia).
rewrite length_skipn, length_firstn, Hlb.
replace (j - length bs - (Nat.min 24 32 - length bs))%nat with (j - 24)%nat by lia.
destruct (Nat.lt_ge_cases j 26) as [J3|J3].
{ assert (j = 24 \/ j = 25)%nat as [-> | ->] by lia; cbn [Nat.sub app nth].
  - split; [| unfold u8; apply Z.mod_pos_bound; lia].
    apply (ceo_val1 _ _ (Z.of_nat (length bs))); [exact H24 | unfold u8; rewrite Z.mod_mod by lia; reflexivity].
  - split; [| unfold u8; apply Z.mod_pos_bound; lia].
    apply (ceo_val1 _ _ disp); [exact H25 | unfold u8; rewrite Z.mod_mod by lia; reflexivity]. }
replace (j - 24)%nat with (S (S (j - 26)))%nat by lia. cbn [app nth].
destruct (Nat.lt_ge_cases j 28) as [J4|J4].
{ rewrite app_nth1 by (rewrite length_firstn, length_skipn, Hlb; cbn; lia).
  rewrite ceo_nth_firstn by lia. rewrite ceo_nth_skipn. replace (26 + (j - 26))%nat with j by lia.
  apply KB; lia. }
rewrite app_nth2 by (rewrite length_firstn, length_skipn, Hlb; cbn; lia).
rewrite length_firstn, length_skipn, Hlb. cbn [Nat.min Nat.sub].
assert (Hk' : forall i, (i < 4)%nat -> mbyte tfibsegs (mrestrict H mem2) (out + Z.of_nat (28 + i)) =
  Some (Z_to_bv 8 (key / 2 ^ (8 * Z.of_nat i)))).
{ intros i Hi. replace (out + Z.of_nat (28 + i)) with (out + 28 + Z.of_nat i) by lia. apply Hk. lia. }
assert (j = 28 \/ j = 29 \/ j = 30 \/ j = 31)%nat as [-> | [-> | [-> | ->]]] by lia; cbn [Nat.sub nth le4Z];
(split; [| apply Z.mod_pos_bound; lia]).
- apply (ceo_val1 _ _ (key / 2 ^ (8 * Z.of_nat 0))); [exact (Hk' 0%nat ltac:(lia)) |].
  cbn [Z.of_nat]. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r, Z.mod_mod by lia. reflexivity.
- apply (ceo_val1 _ _ (key / 2 ^ (8 * Z.of_nat 1))); [exact (Hk' 1%nat ltac:(lia)) |].
  cbn [Z.of_nat]. change (2 ^ (8 * 1)) with 256. rewrite Z.mod_mod by lia. reflexivity.
- apply (ceo_val1 _ _ (key / 2 ^ (8 * Z.of_nat 2))); [exact (Hk' 2%nat ltac:(lia)) |].
  cbn [Z.of_nat]. change (2 ^ (8 * 2)) with 65536. rewrite Z.mod_mod by lia. reflexivity.
- apply (ceo_val1 _ _ (key / 2 ^ (8 * Z.of_nat 3))); [exact (Hk' 3%nat ltac:(lia)) |].
  cbn [Z.of_nat]. change (2 ^ (8 * 3)) with 16777216. rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* a failing return: a0 = rc and out as it was *)
Lemma ceo_res_fail : forall (W : world tfibsegs) memc mem2 regs2 out before sp rc,
garr8 tfibsegs (mrestrict (w_H W) memc) out before -> length before = 32%nat ->
0 <= out -> out + 32 <= 2 ^ 64 -> (out + 32 <= sp - 16 \/ sp <= out) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 16 <= a < sp) -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a) ->
getr regs2 10 = w64 rc ->
cenc_res tfibsegs out before (rc, None) W mem2 regs2.
Proof.
intros W memc mem2 regs2 out before sp rc HG HL Ho Ho2 Hcw KE H10. unfold cenc_res. cbn [fst snd cmd_outZ].
split; [exact H10|]. apply (ceo_garr8_kept (w_H W) memc mem2 out before HG).
intros a Ha. rewrite HL in Ha. cbn in Ha. apply KE; lia.
Qed.
(* KE over the save area gives KE over ceo_zone *)
Lemma ceo_KE_widen : forall H (m m0 : word -> option byte) sp out n,
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 16 <= a < sp) -> aview tfibsegs H m a = aview tfibsegs H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ ceo_zone sp out n a -> aview tfibsegs H m a = aview tfibsegs H m0 a.
Proof. intros H m m0 sp out n KE a Ha Hz. apply KE; [exact Ha|]. intros X. apply Hz. left. exact X. Qed.
(* zdisj of a window of out and an extent that lies off [out, out + 32) *)
Lemma ceo_zdisj : forall out lo hi a b, 0 <= lo -> hi <= 32 -> (out + 32 <= a \/ b <= out) ->
zdisj (out + lo, out + hi) (a, b).
Proof. intros out lo hi a b Hlo Hhi H. unfold zdisj. cbn [fst snd]. lia. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* ================================ out and the image ================================ *)
Lemma ceo_byte_off_img : forall lyc Sc (W : world tfibsegs) memc mdc q n a,
AR tfibsegs B lyc Sc W memc mdc -> tdst_ok B lyc Sc q n -> q <= a < q + n ->
a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a.
Proof.
intros lyc Sc W memc mdc q n a HAR Hd Ha.
destruct (Hd a Ha) as [(b & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- pose proof (blk_off_img B lyc Sc W memc mdc b m HAR Hin) as Ho. unfold off_img in Ho. lia.
- pose proof (frm_off_img B lyc Sc W memc mdc cid pos HAR Hin) as Ho. unfold off_img in Ho.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. lia.
Qed.
Lemma ceo_off_img : forall STK sp0 FP ly S lyc Sc own (W : world tfibsegs) memc mdc sp T out,
AR tfibsegs B lyc Sc W memc mdc -> cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp T out 32 ->
out + 32 <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= out.
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc sp T out HAR (_ & _ & Htd & _).
destruct (Z_le_gt_dec (out + 32) YImgTop.IMG_LO) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec YImgTop.IMG_TOP out) as [H2|H2]; [right; exact H2|].
exfalso. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
destruct (ceo_byte_off_img lyc Sc W memc mdc out 32 (Z.max out 0x10000) HAR Htd ltac:(lia)) as [H3|H3];
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in H3; lia.
Qed.
(* the leaf's E: no byte out writes is a byte of the image *)
Lemma ceo_eimg : forall STK sp0 FP ly S lyc Sc own (W : world tfibsegs) memc mdc sp T out a,
AR tfibsegs B lyc Sc W memc mdc -> cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp T out 32 ->
cenc_wr out a -> in_img tfibsegs a -> False.
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc sp T out a HAR (_ & _ & Htd & _) Ha Him.
exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 a HAR Htd Ha Him).
Qed.

(* ================================ entry ================================ *)
Lemma ceo_entry : forall pc xs (m : nat) (r : bv 5) AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs)
memc mdc k regs T out,
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T -> 16 <= T ->
Z.of_nat m = bv_unsigned r -> getr regs r = w64 out ->
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) T out 32 ->
atoms_ok (Ereg regs (cw_extra xs)) AF ->
st_ok tfibsegs (Ereg regs (cw_extra xs))
(mkSS pc sr_atoms (cw_regs 16) None (mkFacts (cw_atoms ++ ceo_fact m :: AF) [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom tfibsegs))).
Proof.
intros pc xs m r AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T out HE HT Hm Hr HD HAF.
pose proof HE as ((HAR & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HD as (Hq & Hqn & Htd & _).
pose proof (cj_dst_byte tfibsegs B LAWS lyc Sc W memc mdc out 32 out HAR Htd ltac:(lia)) as (Ho1 & _).
apply (cw_entry_base_af B TL LAWS pc 16 xs (ceo_fact m :: AF) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T
  HE ltac:(lia) ltac:(reflexivity)).
cbn [atoms_ok ceo_fact]. split; [|exact HAF]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (cw_ew_reg regs xs m r Hm), Hr. unfold w64. rewrite unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
Qed.

(* ================================ the windows ================================ *)
Lemma ceo_writable : forall STK sp0 FP ly S lyc Sc own (W : world tfibsegs) memc mdc sp T out (mem : word -> option byte) a,
AR tfibsegs B lyc Sc W memc mdc ->
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp T out 32 -> out <= a < out + 32 ->
aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) memc a ->
writable_at tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc sp T out mem a HAR (Hq & Hqn & Htd & Htw & _) Ha Hv.
apply (apresent_writable tfibsegs).
apply (apresent_transfer tfibsegs (w_H W) (w_H W) memc mem a); [lia | | exact Hv | exact (proj1 (proj2 (Htw a Ha)))].
intros Him. exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 a HAR Htd Ha Him).
Qed.
Lemma ceo_add : forall E ss ms (m : nat) out lo hi,
st_ok tfibsegs E ss ms -> bv_unsigned (ew E m) = out -> 0 <= lo <= hi -> 0 <= out -> out + hi <= 2 ^ 64 ->
(forall o, lo <= o < hi -> writable_at tfibsegs (ms_mem ms) (out + o)) ->
all_disjoint E (ceo_win m lo hi) (ss_mem ss) ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (ceo_win m lo hi :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms m out lo hi HS Hb Hlh Ho Hhi Hw Hd. apply ast_ok_add_region; [exact HS | | | exact Hd].
- unfold region_wf, ceo_win. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb].
  rewrite !Z.leb_refl, (proj2 (Z.leb_le lo hi) ltac:(lia)). cbn [andb]. rewrite orb_true_r. reflexivity.
- unfold region_ok, ceo_win. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Hb. split; [lia|]. split; [lia|]. split; [exact Hw | constructor].
Qed.
(* the three windows on top of a state's regions; ceo_disj proves the three all_disjoint premises *)
Lemma ceo_add3 : forall STK sp0 FP ly S lyc Sc own (W : world tfibsegs) memc mdc sp T E ss ms (m : nat) out n,
AR tfibsegs B lyc Sc W memc mdc ->
cdst_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp T out 32 ->
st_ok tfibsegs E ss (restrict (w_H W) ms) -> bv_unsigned (ew E m) = out -> 0 <= n <= 24 ->
(forall a, out <= a < out + 32 -> aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) memc a) ->
all_disjoint E (ceo_win m 28 32) (ss_mem ss) ->
all_disjoint E (ceo_win m 24 26) (ss_mem ss) ->
all_disjoint E (ceo_win m 0 n) (ss_mem ss) ->
st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (ceo_regs m n ++ ss_mem ss) (ss_resv ss) (ss_facts ss))
(restrict (w_H W) ms).
Proof.
intros STK sp0 FP ly S lyc Sc own W memc mdc sp T E ss ms m out n HAR HD HS Hb Hn KE D28 D24 D0.
pose proof HD as (Hq & Hqn & _).
assert (Hw : forall lo hi, 0 <= lo -> hi <= 32 -> forall o, lo <= o < hi ->
  writable_at tfibsegs (ms_mem (restrict (w_H W) ms)) (out + o)).
{ intros lo hi Hlo Hhi o Ho. cbn [ms_mem restrict].
  apply (ceo_writable STK sp0 FP ly S lyc Sc own W memc mdc sp T out (ms_mem ms) (out + o) HAR HD ltac:(lia)).
  apply KE. lia. }
assert (Hx : forall lo hi lo' hi', 0 <= lo -> hi <= lo' -> hi' <= 32 ->
  extent_disjoint E (ceo_win m lo hi) (ceo_win m lo' hi')).
{ intros lo hi lo' hi' H1 H2 H3. unfold extent_disjoint, ceo_win. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. lia. }
pose proof (ceo_add E ss _ m out 28 32 HS Hb ltac:(lia) ltac:(lia) ltac:(lia) (Hw 28 32 ltac:(lia) ltac:(lia)) D28) as S1.
pose proof (ceo_add E _ _ m out 24 26 S1 Hb ltac:(lia) ltac:(lia) ltac:(lia) (Hw 24 26 ltac:(lia) ltac:(lia))
  ltac:(cbn [ss_mem]; split; [apply Hx; lia | exact D24])) as S2.
pose proof (ceo_add E _ _ m out 0 n S2 Hb ltac:(lia) ltac:(lia) ltac:(lia) (Hw 0 n ltac:(lia) ltac:(lia))
  ltac:(cbn [ss_mem]; split; [apply Hx; lia | split; [apply Hx; lia | exact D0]])) as S3.
exact S3.
Qed.
End b.

(* ================================ tactics ================================ *)
(* the walk's env after runs is the entry env under ewset / havoc: read atom n of it from the entry facts
   (B2 : bv_unsigned (ew E 2) = spZ regs, the out atom's bv_unsigned (ew E m) = out, ...) *)
Ltac ceo_env_norm :=
rewrite ?ew_ewset_other, ?ew_havoc_old by lia;
repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => progress rewrite H end.
Ltac ceo_env_norm_in Hb :=
rewrite ?ew_ewset_other, ?ew_havoc_old in Hb by lia;
repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => progress rewrite H in Hb end.
(* all_disjoint E (ceo_win m lo hi) (ss_mem ss) at a stop: side proves out + 32 <= a \/ b <= out for each extent
   (a, b) of the state's other regions (the save area: coff_win; the .got slot and the cell: ceo_off_img) *)
Ltac ceo_disj side :=
idtac; lazymatch goal with
| |- all_disjoint ?E ?r ?rs =>
  let rs' := eval vm_compute in rs in change (all_disjoint E r rs');
  apply all_disjoint_of_extents;
  cbn [List.map zall_disjoint]; unfold extent_of_region, ceo_win;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  ceo_env_norm;
  repeat split;
  first [ apply ceo_zdisj; [lia | lia | side] | match goal with |- ?g => fail 100 "ceo_disj: cannot close" g end ]
| |- ?g => fail 100 "ceo_disj: the goal is not all_disjoint:" g
end.
(* the write-range obligation of a run: read-only regions, the save area of atom 2 (in the caller's stack allowance
   by the contract's two stack-window premises; needs B2 : bv_unsigned (ew _ 2) = ..), and out's windows, paid by
   Htw : twr_ok .. out 32 (cdst_ok's write right) *)
Ltac ceo_awr_go Htw qv nv :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion ?b _ _ ?wlo ?whi _ :: _) _ ?sp0 _ _ _ _ _ =>
  lazymatch eval vm_compute in (Z.leb whi wlo) with
  | true => apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | ceo_awr_go Htw qv nv]
  | false =>
    lazymatch b with
    | Some 2%nat =>
      lazymatch goal with B2 : bv_unsigned (ew _ 2) = ?spv |- _ =>
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
      [reflexivity | ceo_env_norm; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | ceo_awr_go Htw qv nv] end
    | Some ?mv =>
      eapply (cw_awr_ok_cons_twr) with (m := mv) (q := qv) (n := nv);
      [reflexivity | ceo_env_norm; try reflexivity | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | exact Htw | ceo_awr_go Htw qv nv]
    | _ => fail 100 "ceo_awr: a writable region with no base atom"
    end
  end
end.
Ltac ceo_awr Htw :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
lazymatch type of Htw with twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ ?qv ?nv => ceo_awr_go Htw qv nv end.
(* every write window of a state lies in KE's zone: the save area (cw_kwr_stk's) or ceo_zone *)
Ltac ceo_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ceo_env_norm_in Hb;
  try unfold ceo_zone; lia | ]);
destruct Hr.
(* at a stop, the chunks of the regions 0, 1, 2 of HS (out's three windows after ceo_add3), each as a hypothesis
   chunk_ok .. out (mkChunk off (CVal w e)) *)
Ltac ceo_chunks HS :=
let go i :=
  lazymatch type of HS with st_ok _ ?E ?ss _ =>
  let ro := eval vm_compute in (nth_error (ss_mem ss) i) in
  lazymatch ro with Some ?rr =>
  let HR := fresh "HR" in let HCs := fresh "HCs" in
  pose proof (st_ok_region_nth E ss _ i rr HS ltac:(vm_compute; reflexivity)) as HR;
  unfold region_ok in HR;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict] in HR;
  ceo_env_norm_in HR;
  destruct HR as (_ & _ & _ & HCs);
  repeat (let Hc := fresh "HC" in apply Forall_cons_iff in HCs; destruct HCs as [Hc HCs]); clear HCs
  end end in
go 0%nat; go 1%nat; go 2%nat.
(* a0 at `ret` from R10 : getr .. 10 = sv_denot _ (SLit _) *)
Ltac ceo_a0 R10 := rewrite R10; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
