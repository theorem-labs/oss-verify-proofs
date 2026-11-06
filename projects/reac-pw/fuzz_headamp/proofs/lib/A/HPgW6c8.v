(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the block statement
   w6c_case8_stmt of lib/A/HPgW6cBase.v, the walk of ent_build's case 8 (pod.h:360-366) inside
   LLVMFuzzerTestOneInput (0x80bc0), from the case entry 0x81e18 to the join J 0x8237c. Proves no function (kind:
   segment lemma).

   THE CODE (registers as HPgW6cBase names them: s1 = R, s7 = SHADOW_OFF, s8 = cur, s9 = |r|, a4 = cur - 1).
     0x81e18  beqz s9 -> 0x82138                    no byte left
     0x81e1c .. 0x81e28  the shadow check of s8 (NE-SLOW, slow block 0x826dc)
     0x81e2c  lbu a1,0(s8) (= t); a1 := t & 3; a0 := 0x21100 + 4 (t & 3)   (ent_build.t.9)
     0x81e44 .. 0x81e50  the shadow check of a0, 4 bytes (NE-SLOW, slow block 0x826e8)
     0x81e54  lw a0,0(a0) (= t.9[t & 3]); s4 := [R+0x118] - 2; s8 := a4 + 2; sw a0,0([R+0x110]) (e.type);
              a3 := [R+0xe0] (= e.body); beq a1,3 -> 0x81ee0
     0x81e78  beqz s4 -> 0x81ee0
     0x81e7c .. 0x81e88  the shadow check of s8 (NE-SLOW, slow block 0x8279c)
     0x81e8c  lbu a2,0(s8) (= s); s4 := [R+0x118] - 3; s8 := a4 + 3; a2 := s & 3; j 0x82150
     0x81ee0  a2 := 0; j 0x82150
     0x82138  s4 := 0; a2 := 0; sw 4,0([R+0x110]) (e.type); a3 := [R+0xe0]
     0x82150  sw a2,4([R+0x110]) (e.size); a0 := a3; a1 := 0; jal __asan_memset   (lib/A/HPgW6cTail.v takes it on)

   THE PROOF is cut by the length of the input after the kind byte, because the engine's bound on the cell
   [R+0x118] must be a closed numeral (a term in |r| inside a fact makes its vm_compute grow without end):
     w6c8_nil  r = []              N = 1, regions [RS; RE],        s9 pinned to 0
     w6c8_one  r = [b]             N = 2, regions [RS; RE; RI 1]
     w6c8_two  r = b :: s :: r2    N >= 3, regions [RS; RE; RI 2]
   Each of the last two splits on j = t mod 4 (four arms), pins a0 and a1 to the literal address and index the
   table load needs, drops the input region and adds the table region (the contract does not place the input
   outside the image, so the two may not be regions of one state), and for j <> 3 with a byte left drops the table
   again and adds the second input byte. j = 3 (t.9[3] = POD_STRING) takes `beq a1,3`; with one byte left the
   value of s4 is 0, which the engine's interval of [R+0x118] cannot decide, so s4 is pinned there. Nine leaves in
   all; each ends with lib/A/HPgW6cTail.v's w6c_tail_set re-seated by w6c_jpost_trans. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSteps HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW6cTail HPgW6cEng HPgW6cBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================= the model of case 8 ======================= *)
Lemma w6c8_model : forall (r : list byte), w6c_ent 8 r =
  (let (t, r1) := Cursor.fuzz_u8 r in
   let ty := nth (Z.to_nat (t mod 4)) Tables.t8 0 in
   if ty =? POD_STRING then (Ent POD_STRING 0 [], r1)
   else (let (s, r2) := Cursor.fuzz_u8 r1 in (Ent ty (s mod 4) (zeros (Z.to_nat (s mod 4))), r2))).
Proof.
intros r. unfold w6c_ent, ent_build. cbn [Cursor.fuzz_u8].
replace (bv_unsigned (Z_to_bv 8 8)) with 8 by (vm_compute; reflexivity).
reflexivity.
Qed.

Lemma w6c8_e0 : w6c_ent 8 [] = (Ent 4 0 (zeros (Z.to_nat 0)), []).
Proof. rewrite w6c8_model. cbn [Cursor.fuzz_u8]. reflexivity. Qed.

Lemma w6c8_e1 : forall (b : byte) j, bv_unsigned b mod 4 = j -> 0 <= j < 4 ->
  w6c_ent 8 [b] = (Ent (nth (Z.to_nat j) Tables.t8 0) 0 (zeros (Z.to_nat 0)), []).
Proof.
intros b j Hj Hr. rewrite w6c8_model. cbn [Cursor.fuzz_u8]. rewrite Hj.
assert (H : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
destruct H as [H0|[H0|[H0|H0]]]; rewrite H0; reflexivity.
Qed.

Lemma w6c8_e2 : forall (b s' : byte) (r2 : list byte) j, bv_unsigned b mod 4 = j -> 0 <= j < 4 -> j <> 3 ->
  w6c_ent 8 (b :: s' :: r2) =
  (Ent (nth (Z.to_nat j) Tables.t8 0) (bv_unsigned s' mod 4) (zeros (Z.to_nat (bv_unsigned s' mod 4))), r2).
Proof.
intros b s' r2 j Hj Hr Hn3. rewrite w6c8_model. cbn [Cursor.fuzz_u8]. rewrite Hj.
assert (H : j = 0 \/ j = 1 \/ j = 2) by lia.
destruct H as [H0|[H0|H0]]; rewrite H0; reflexivity.
Qed.

Lemma w6c8_e3 : forall (b s' : byte) (r2 : list byte), bv_unsigned b mod 4 = 3 ->
  w6c_ent 8 (b :: s' :: r2) = (Ent 8 0 (zeros (Z.to_nat 0)), s' :: r2).
Proof. intros b s' r2 Hj. rewrite w6c8_model. cbn [Cursor.fuzz_u8]. rewrite Hj. reflexivity. Qed.

Lemma w6c8_t8_0 : nth (Z.to_nat 0) Tables.t8 0 = 4. Proof. reflexivity. Qed.
Lemma w6c8_t8_1 : nth (Z.to_nat 1) Tables.t8 0 = 6. Proof. reflexivity. Qed.
Lemma w6c8_t8_2 : nth (Z.to_nat 2) Tables.t8 0 = 2. Proof. reflexivity. Qed.
Lemma w6c8_t8_3 : nth (Z.to_nat 3) Tables.t8 0 = 8. Proof. reflexivity. Qed.

(* ======================= what a run of this piece may write ======================= *)
(* every region of every state here either has no write window, or is R's cells [R+0x118, R+0x120), or is e's
   header [F+0xf0, F+0xf8) *)
Definition w6c8_wok (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r)
  || match YP09.r_base r with
     | Some n => (Nat.eqb n 9 && (0x118 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0x120))
                 || (Nat.eqb n 32 && (0xf0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0xf8))
     | None => false
     end.

Definition w6c8_out (R F a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ ~ (R + 0x118 <= a < R + 0x120) /\ ~ (F + 0xf0 <= a < F + 0xf8).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma w6c8_kept : forall E rs (H : word -> bool) m m' R F,
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F -> forallb w6c8_wok rs = true ->
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forall a, w6c8_out R F a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' R F U9 U32 Hall HF a (Ha & H1 & H2).
apply (aview_eq_of rsegs). rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hall r Hin) as Hw.
rewrite unsigned_lit_small in Hr by lia.
destruct r as [rb rlo rhi rwlo rwhi rcs].
unfold w6c8_wok in Hw.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hw, Hr.
apply orb_prop in Hw as [Hw|Hw].
- apply Z.leb_le in Hw. lia.
- destruct rb as [n|]; [|discriminate Hw].
  cbn [base_val] in Hr.
  apply orb_prop in Hw as [Hw|Hw]; apply andb_prop in Hw as [Hw Hhi];
    apply andb_prop in Hw as [Hn Hlo]; apply Nat.eqb_eq in Hn; subst n;
    apply Z.leb_le in Hlo; apply Z.leb_le in Hhi.
  + rewrite U9 in Hr. lia.
  + rewrite U32 in Hr. lia.
Qed.

Lemma w6c8_awr : forall E rs STK sp0 FP bl0 blc ly own R F,
  bv_unsigned (ew E 9) = R -> bv_unsigned (ew E 32) = F ->
  sp0 - STK <= R + 0x118 -> R + 0x120 <= sp0 ->
  (forall a, F + 0xf0 <= a < F + 0xf8 -> awr_byte STK sp0 FP bl0 blc ly own a) ->
  forallb w6c8_wok rs = true ->
  awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs STK sp0 FP bl0 blc ly own R F U9 U32 Hlo Hhi HF Hall a (r & Hin & Ha).
pose proof (proj1 (forallb_forall _ _) Hall r Hin) as Hw.
destruct r as [rb rlo rhi rwlo rwhi rcs].
unfold w6c8_wok in Hw.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hw, Ha.
apply orb_prop in Hw as [Hw|Hw].
- apply Z.leb_le in Hw. lia.
- destruct rb as [n|]; [|discriminate Hw].
  cbn [base_val] in Ha.
  apply orb_prop in Hw as [Hw|Hw]; apply andb_prop in Hw as [Hw Hhi'];
    apply andb_prop in Hw as [Hn Hlo']; apply Nat.eqb_eq in Hn; subst n;
    apply Z.leb_le in Hlo'; apply Z.leb_le in Hhi'.
  + rewrite U9 in Ha. left. lia.
  + rewrite U32 in Ha. apply HF. lia.
Qed.

(* the shadow byte of an application address and a byte of the input are outside the write set *)
Lemma w6c8_sh_out : forall R F x, 0 <= x < kHighMemEnd -> in_app F 1024 -> kHighMemBeg <= R ->
  w6c8_out R F (shadow_of_addr SHADOW_OFF x).
Proof.
intros R F x Hx HF HR. pose proof (hm_shadow_band x Hx) as Hb.
pose proof (hm_shadow_not_app x F 1024 Hx HF) as Hn.
unfold w6c8_out, kLowMemEnd, kHighMemBeg in *. repeat split; lia.
Qed.

Lemma w6c8_ra_keep : forall (W : world rsegs) m m' R F a n,
  range_addressable (aview rsegs (w_H W) m) SHADOW_OFF a n ->
  (forall x, w6c8_out R F x -> aview rsegs (w_H W) m' x = aview rsegs (w_H W) m x) ->
  (forall x, a <= x < a + n -> w6c8_out R F (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview rsegs (w_H W) m') SHADOW_OFF a n.
Proof.
intros W m m' R F a n Hra KE Hs x Hx. destruct (Hra x Hx) as (s & Hv & Ho).
exists s. split; [rewrite (KE _ (Hs x Hx)); exact Hv | exact Ho].
Qed.

Lemma w6c8_shok_any : forall (W : world rsegs) E memc m R F,
  bv_unsigned (ew E 23) = SHADOW_OFF -> bv_unsigned (ew E 32) = F ->
  0 <= F -> F + 1024 <= 2 ^ 47 -> in_app F 1024 -> kHighMemBeg <= R ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0xf0) 8 ->
  (forall a, w6c8_out R F a -> aview rsegs (w_H W) m a = aview rsegs (w_H W) memc a) ->
  sh_ok rsegs w6c_Bx w6c_SH E (mrestrict (w_H W) m).
Proof.
intros W E memc m R F U23 U32 HF0 HF47 HFapp HR Hra KE.
apply (w6c_shok E W m F).
- unfold w6c_Bx. rewrite U_SOff, U23, Z.add_0_r. apply zcanon_id. unfold SHADOW_OFF, M64. lia.
- rewrite U_SOff, U32, Z.add_0_r. apply zcanon_id. unfold M64. lia.
- apply (w6c8_ra_keep W memc m R F (F + 0xf0) 8); [exact Hra | exact KE|].
  intros x Hx. apply w6c8_sh_out; [unfold kHighMemEnd; lia | exact HFapp | exact HR].
- exact HFapp.
Qed.

(* the 16 table bytes are read-only: a run of this piece keeps them *)
Lemma w6c8_RT_keep : forall E (W : world rsegs) m m' tb,
  region_ok rsegs E (mrestrict (w_H W) m) (w6c_RT tb) ->
  (forall x, tb <= x < tb + 16 -> aview rsegs (w_H W) m' x = aview rsegs (w_H W) m x) ->
  region_ok rsegs E (mrestrict (w_H W) m') (w6c_RT tb).
Proof.
intros E W m m' tb HR K. unfold w6c_RT, region_ok in *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *.
destruct HR as (H1 & H2 & H3 & H4).
split; [exact H1|]. split; [exact H2|]. split; [intros o Ho; exfalso; lia|].
inversion H4 as [|cc ccs Hck Hrest Eqq]; subst. constructor; [|constructor].
intros i Hi. change (YP09.c_len (YP09.mkChunk tb (CImg 16))) with 16 in Hi.
destruct (Hck i Hi) as (bb & Hb & Hm). exists bb. split; [exact Hb|].
rewrite <- Hm. apply (mbyte_of_aview rsegs (w_H W) (w_H W) m m').
apply K. cbn [YP09.c_off]. lia.
Qed.

(* one byte of a byte list that memory holds, and the two zero words of e's header *)
Lemma w6c8_byte : forall (H : word -> bool) mem a (l : list byte) (i : nat),
  hm_bytes rsegs H mem a l -> (i < length l)%nat ->
  val_mem rsegs (mrestrict H mem) (a + Z.of_nat i) 1 (bv_unsigned (nth i l (Z_to_bv 8 0))).
Proof.
intros H mem a l i Hb Hi.
exact (proj1 (hm_aview_val1 rsegs H mem _ _ (proj1 (hm_bytes_aview rsegs H mem a l) Hb i Hi))).
Qed.

Lemma w6c8_hdr0 : forall (H : word -> bool) mem a, hm_bytes rsegs H mem a (zeros 104) ->
  val_mem rsegs (mrestrict H mem) a 4 0 /\ val_mem rsegs (mrestrict H mem) (a + 4) 4 0.
Proof.
intros H mem a Hb. split.
- pose proof (hm_bytes_slice rsegs H mem a (zeros 104) 0 4 Hb ltac:(rewrite length_zeros; lia)) as Hs.
  pose proof (hm_bytes_val rsegs H mem _ _ Hs) as Hv.
  replace (a + Z.of_nat 0) with a in Hv by lia.
  change (length (hm_slice (zeros 104) 0 4)) with 4%nat in Hv.
  change (bytes_le_to_Z (hm_slice (zeros 104) 0 4)) with 0 in Hv. exact Hv.
- pose proof (hm_bytes_slice rsegs H mem a (zeros 104) 4 4 Hb ltac:(rewrite length_zeros; lia)) as Hs.
  pose proof (hm_bytes_val rsegs H mem _ _ Hs) as Hv.
  replace (a + Z.of_nat 4) with (a + 4) in Hv by lia.
  change (length (hm_slice (zeros 104) 4 4)) with 4%nat in Hv.
  change (bytes_le_to_Z (hm_slice (zeros 104) 4 4)) with 0 in Hv. exact Hv.
Qed.

Lemma w6c8_denot_of_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
End b.

(* a register of a run's final state is its symbolic value, read off the state *)
Ltac w6c8_regv HS W r :=
  rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ _ r HS);
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity)
  end;
  cbn [sv_denot].
(* an atom of the env of a later run is the atom of the entry's env *)
Ltac w6c8_ew := rewrite ?ew_ewset_other by lia; eassumption.
Ltac w6c8_in := cbv [w6c_keep In]; repeat (first [ left; reflexivity | right ]).
Ltac w6c8_inc := cbv [In]; repeat (first [ left; reflexivity | right ]).
(* the memory of the state after a run still agrees with the entry's outside the write set *)
Ltac w6c8_step KEold KEnew RR FF :=
  lazymatch goal with
  | HFr : frame_of ?E ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
    lazymatch type of KEold with
    | forall a, _ -> _ = aview _ _ ?mc a =>
      assert (KEnew : forall a, w6c8_out RR FF a -> aview rsegs H m1 a = aview rsegs H mc a) by
        (intros a Ha;
         rewrite (w6c8_kept E rs H m0 m1 RR FF ltac:(w6c8_ew) ltac:(w6c8_ew)
           ltac:(vm_compute; reflexivity) HFr a Ha);
         exact (KEold a Ha));
      clear HFr KEold
    end
  end.
Ltac w6c8_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; w6c8_kio].
Ltac w6c8_clean :=
  repeat match goal with
  | H : frame_of _ _ _ _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end;
  repeat match goal with old : machine_state |- _ => clear old end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6C_SET.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

(* ======================= the leaf: the call's entry, then the tail ======================= *)
Lemma w6c8_fin : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa r
  E ss ms md ty sz cur' nl',
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa r ->
st_ok rsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = W6C_SET ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
same_io mdc md ->
(forall rr, In rr w6c_keep -> getr (ms_regs ms) rr = getr regs rr) ->
getr (ms_regs ms) 1 = w64 W6C_RSET -> getr (ms_regs ms) 10 = w64 (F + 0xf8) ->
getr (ms_regs ms) 11 = w64 0 -> getr (ms_regs ms) 12 = w64 sz ->
getr (ms_regs ms) 20 = w64 nl' -> getr (ms_regs ms) 24 = w64 cur' ->
0 <= sz <= 96 ->
(forall a, w6c8_out R F a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xf0) 4 ty ->
val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xf4) 4 sz ->
SRr rsegs W (mkCfg ms md)
  (w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
     (Ent ty sz (zeros (Z.to_nat sz))) cur' nl' sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa r
  E ss ms md ty sz cur' nl' Hctx Hin HS Hrv Hpc HJ2 Hio Hk H1 H10 H11 H12 H20 H24 Hsz KE Vt Vs.
pose proof Hctx as Hctx0. destruct Hctx as (HJ & HG & HROM).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HFeq & HFapp & HF32).
destruct Hin as (D2 & D3 & D4 & D9 & D23 & D24 & D14 & D25 & Dm0 & Db0 & Dsa & Dc0 & Df0 & Df8 &
  Dez & Dfsh & Drm & Dra & Dhull & Damr & Dcur1 & Dcur2 & Ddisj & Dt6 & Dt8 & Dtf).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
unfold kHighMemBeg, T_SEG_STK, ASTACK in HRk, HSTK, HRc.
(* the write set keeps every byte of e above its header and every byte of R's cells below 0xf8 *)
assert (HM : forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0xf0 <= a < F + 0x158) ->
  ~ (R + 0x118 <= a < R + 0x120) -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Ha1 Ha2 Ha3. apply KE. unfold w6c8_out. split; [exact Ha|]. split; [exact Ha3 | lia]. }
rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS Hrv) at 1. rewrite Hpc.
eapply SRr_mono.
{ apply (w6c_tail_set B AMEMSET STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms) md
    (ms_regs ms) R F pos ty sz cur' nl' sa HJ2 HG H1).
  - rewrite (Hk (2%bv) ltac:(w6c8_in)). exact D2.
  - rewrite (Hk (3%bv) ltac:(w6c8_in)). exact D3.
  - rewrite (Hk (4%bv) ltac:(w6c8_in)). exact D4.
  - rewrite (Hk (9%bv) ltac:(w6c8_in)). exact D9.
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H20.
  - exact H24.
  - exact Hsz.
  - exact Dsa.
  - (* e's 104 bytes from the two header words *)
    apply (w6c_e_hdr (w_H W) memc (ms_mem ms) F ty sz Dez Vt Vs).
    intros x Hx. apply KE. unfold w6c8_out. repeat split; lia.
  - (* the frame's shadow bytes are outside the write set *)
    assert (HlenPJ : Z.of_nat (length hs_PJ) = 80) by (vm_compute; reflexivity).
    intros i Hi. rewrite <- (Dfsh i Hi). rewrite HlenPJ in Hi. apply KE.
    pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF.
    pose proof (Z.div_mod R 8 ltac:(lia)) as DR. pose proof (Z.mod_pos_bound R 8 ltac:(lia)) as MR.
    pose proof HFapp as HFapp'. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp'.
    unfold shadow_addr, SHADOW_OFF, w6c8_out.
    destruct HFapp' as (HFa & [HFlo | (HFhi1 & HFhi2)]); repeat split; lia.
  - (* [R+0xd0] is below the written window of R's cells *)
    apply (w6c_val_kept (w_H W) memc (w_H W) (ms_mem ms)); [exact Db0|].
    intros i Hi. apply KE. unfold w6c8_out. repeat split; lia. }
cbv beta. intros W2 c2 _ HP.
exact (w6c_jpost_trans B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs (ms_mem ms) md
  (ms_regs ms) R F _ cur' nl' sa W2 c2 Hk Hio HM HP).
Qed.

(* ======================= the three input-length cases ======================= *)
Lemma w6c8_nil : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa,
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa [] ->
SRr rsegs W (cfg_at rsegs W6C_D8 regs memc mdc)
  (w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
     (fst (w6c_ent 8 [])) (cur + Z.of_nat (length (@nil byte) - length (snd (w6c_ent 8 []))))
     (Z.of_nat (length (snd (w6c_ent 8 [])))) sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa Hctx Hin.
pose proof Hctx as Hctx0. pose proof Hin as Hin0.
destruct Hctx as (HJ & HG & HROM).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
destruct (w6c_present B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx0) as (HprF & HprR).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HFeq & HFapp & HF32).
destruct Hin as (D2 & D3 & D4 & D9 & D23 & D24 & D14 & D25 & Dm0 & Db0 & Dsa & Dc0 & Df0 & Df8 &
  Dez & Dfsh & Drm & Dra & Dhull & Damr & Dcur1 & Dcur2 & Ddisj & Dt6 & Dt8 & Dtf).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
cbn [length] in D25, Df8, Dcur2.
assert (Hed : fst (w6c_ent 8 []) = Ent 4 0 (zeros (Z.to_nat 0))) by (rewrite w6c8_e0; reflexivity).
assert (Hcc : cur + Z.of_nat (length (@nil byte) - length (snd (w6c_ent 8 []))) = cur)
  by (rewrite w6c8_e0; cbn [snd length Nat.sub]; lia).
assert (Hnn : Z.of_nat (length (snd (w6c_ent 8 []))) = 0) by (rewrite w6c8_e0; cbn [snd length]; lia).
rewrite Hed, Hcc, Hnn. clear Hed Hcc Hnn.
pose proof w6c_wx as Hwx. pose proof w6c_segs_low as Hsl. pose proof LAWS as HL.
assert (HAE : env_agree 32 (Ereg regs (w6c_extra F 1 0 sa 0)) (Ereg regs (w6c_extra F 1 0 sa 0)))
  by apply env_agree_refl.
assert (U9 : bv_unsigned (ew (Ereg regs (w6c_extra F 1 0 sa 0)) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 (9%bv) eq_refl), D9. apply unsigned_lit_small.
  unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia. }
assert (U32 : bv_unsigned (ew (Ereg regs (w6c_extra F 1 0 sa 0)) 32) = F).
{ rewrite (w6c_e32 regs F 1 0 sa 0). apply unsigned_lit_small. lia. }
assert (U23 : bv_unsigned (ew (Ereg regs (w6c_extra F 1 0 sa 0)) 23) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs _ 23 (23%bv) eq_refl), D23. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (U14 : bv_unsigned (ew (Ereg regs (w6c_extra F 1 0 sa 0)) 14) = cur - 1).
{ rewrite (ew_Ereg_nat regs _ 14 (14%bv) eq_refl), D14. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs (w6c_extra F 1 0 sa 0)) 32 = w64 F) by apply (w6c_e32 regs F 1 0 sa 0).
assert (E33 : ew (Ereg regs (w6c_extra F 1 0 sa 0)) 33 = w64 1) by apply (w6c_e33 regs F 1 0 sa 0).
assert (E35 : ew (Ereg regs (w6c_extra F 1 0 sa 0)) 35 = w64 sa) by apply (w6c_e35 regs F 1 0 sa 0).
destruct (w6c8_hdr0 (w_H W) memc (F + 0xf0) Dez) as (Vz0 & Vz4).
replace (F + 0xf0 + 4) with (F + 0xf4) in Vz4 by lia.
assert (HraE : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0xf0) 8).
{ replace (F + 0xf0) with (F + HM_E + 0) by (unfold HM_E; lia).
  apply (hm_A_ra_e rsegs _ _ F false false false false false 0 8);
    [rewrite <- hs_PJ_sh; exact Dfsh | apply w6c_F8; exact HF32 | lia | lia]. }
assert (KE : forall a, w6c8_out R F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
assert (SHOK : sh_ok rsegs w6c_Bx w6c_SH (Ereg regs (w6c_extra F 1 0 sa 0)) (mrestrict (w_H W) memc)).
{ apply (w6c8_shok_any W (Ereg regs (w6c_extra F 1 0 sa 0)) memc memc R F U23 U32 ltac:(lia) ltac:(lia) HFapp
    ltac:(unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia) HraE KE). }
(* the entry state *)
assert (HS0 : st_ok rsegs (Ereg regs (w6c_extra F 1 0 sa 0))
  (mkSS W6C_D8 sr_atoms [w6c_RS; w6c_RE] None (mkFacts (w6c_facts 1 1 (2 ^ 47 - 2)) [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6C_D8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (w6c_RS_ok (Ereg regs (w6c_extra F 1 0 sa 0)) W memc R F 1 sa U9 E32 E33 E35);
        [unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia | lia | lia | lia | lia | lia
        | intros o Ho; apply HprR; lia | exact Dm0 | exact Db0 | exact Dc0 | exact Df0 | exact Df8].
    + apply (w6c_RE_ok (Ereg regs (w6c_extra F 1 0 sa 0)) W memc F U32);
        [lia | lia | intros o Ho; apply HprF; lia | exact Vz0 | exact Vz4].
  - cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint, w6c_RS, w6c_RE, base_val.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U9, U32. unfold T_SEG_STK, ASTACK in *.
    split; [split; [right; lia | exact I] | split; exact I].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
    apply (w6c_facts_ok (Ereg regs (w6c_extra F 1 0 sa 0)) R F (cur - 1) 1 0 0 1 1 (2 ^ 47 - 2) U9 U32 U23 U14);
      [rewrite (w6c_e33 regs F 1 0 sa 0); apply unsigned_lit_small; lia
      | rewrite (w6c_e34 regs F 1 0 sa 0); apply unsigned_lit_small; lia
      | rewrite (w6c_e36 regs F 1 0 sa 0); apply unsigned_lit_small; lia
      | unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia | exact HR16 | lia | exact HF32
      | lia | lia | lia | lia]. }
(* s8 = a4 + 1 and s9 = 0 *)
pose proof (w6c_pin (Ereg regs (w6c_extra F 1 0 sa 0)) _ _ (24%bv) (SOff 14 1) HS0 eq_refl
  ltac:(cbn [ss_regs]; replace (sr_get sr_atoms (24%bv : bv 5)) with (SOff 24 0) by (vm_compute; reflexivity);
        cbn [sv_denot]; rewrite U14, (ew_Ereg_nat regs _ 24 (24%bv) eq_refl), D24;
        rewrite unsigned_lit_small by lia; f_equal; lia)) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1. clear HS0.
pose proof (st_ok_pin_lit rsegs _ _ _ (25%bv) 0 HS1 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite D25; reflexivity)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS. clear HS1.
unfold cfg_at. change (w64 W6C_D8) with (Z_to_bv 64 W6C_D8).
aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET.
{ eapply (w6c8_awr (Ereg regs (w6c_extra F 1 0 sa 0)) _ STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own R F U9 U32);
    [unfold T_SEG_STK, ASTACK in *; lia | lia | intros a Ha; apply HFw; lia | vm_compute; reflexivity]. }
w6c8_step KE KE1 R F.
w6c8_clean.
(* the leaf *)
lazymatch goal with HS : st_ok _ ?Ef ?ssf (restrict _ ?ms) |- _ =>
  let r1 := eval vm_compute in (nth_error (ss_mem ssf) 1) in
  lazymatch r1 with Some ?rg =>
    assert (HRE : region_ok rsegs Ef (ms_mem (restrict (w_H W) ms)) rg)
      by (apply (w6c_region_nth Ef ssf _ 1 rg HS); vm_compute; reflexivity)
  end
end.
lazymatch goal with HS : st_ok _ ?Ef _ (restrict _ ?ms) |- _ =>
  assert (U32f : bv_unsigned (ew Ef 32) = F) by w6c8_ew;
  assert (Vt : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xf0) 4 4)
    by (apply (w6c_field Ef _ 32%nat F _ _ _ _ _ 0xf0 4 (SLit 4) 4 HRE U32f ltac:(w6c8_inc));
        [reflexivity | cbn; lia | cbn; lia]);
  assert (Vs : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0xf4) 4 0)
    by (apply (w6c_field Ef _ 32%nat F _ _ _ _ _ 0xf4 4 (SLit 0) 0 HRE U32f ltac:(w6c8_inc));
        [reflexivity | cbn; lia | cbn; lia])
end.
lazymatch goal with HS : st_ok _ ?Ef ?ssf (restrict _ ?ms) |- _ =>
  apply (w6c8_fin STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa []
    Ef ssf ms _ 4 0 cur 0 Hctx0 Hin0 HS eq_refl eq_refl HJ)
end.
- w6c8_kio.
- intros rr Hrr. lazymatch goal with HS : st_ok _ ?Ef _ _ |- _ =>
    apply (regs_kept_of_st_ok rsegs Ef _ _ regs (w6c_extra F 1 0 sa 0) (w_H W)
      [1; 10; 11; 12; 13; 14; 15; 16; 17; 20; 24; 25]%bv HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity) rr) end.
  + cbv [w6c_keep In] in Hrr. repeat (destruct Hrr as [<-|Hrr]; [vm_compute; discriminate|]). destruct Hrr.
  + cbv [w6c_keep In] in Hrr.
    repeat (destruct Hrr as [<-|Hrr]; [cbv [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]).
    destruct Hrr.
- lazymatch goal with HS : st_ok _ _ _ _ |- _ => w6c8_regv HS W (1%bv : bv 5) end. reflexivity.
- lazymatch goal with HS : st_ok _ ?Ef _ _ |- _ => w6c8_regv HS W (10%bv : bv 5);
    assert (E32f : ew Ef 32 = w64 F) by w6c8_ew; rewrite E32f end.
  unfold w64. rewrite unsigned_lit_small by lia. f_equal; lia.
- lazymatch goal with HS : st_ok _ _ _ _ |- _ => w6c8_regv HS W (11%bv : bv 5) end. reflexivity.
- lazymatch goal with HS : st_ok _ _ _ _ |- _ => w6c8_regv HS W (12%bv : bv 5) end. reflexivity.
- lazymatch goal with HS : st_ok _ _ _ _ |- _ => w6c8_regv HS W (20%bv : bv 5) end. reflexivity.
- lazymatch goal with HS : st_ok _ ?Ef _ _ |- _ => w6c8_regv HS W (24%bv : bv 5);
    assert (U14f : bv_unsigned (ew Ef 14) = cur - 1) by w6c8_ew; rewrite U14f end.
  unfold w64. f_equal; lia.
- lia.
- exact KE1.
- exact Vt.
- exact Vs.
Qed.

(* a register of a run's final state, read off the state (the env comes from the hypothesis) *)
Ltac w6c8_regn HS r :=
  rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS);
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity)
  end;
  cbn [sv_denot].

(* with one byte left s4 is [R+0x118] - 2 = 0, which the engine's interval of [R+0x118] cannot decide *)
Ltac w6c8_pin20 :=
  lazymatch goal with HS : st_ok _ ?Ef ?ssf (restrict _ ?ms) |- _ =>
    let H33 := fresh "H33p" in
    assert (H33 : bv_unsigned (ew Ef 33) = 2) by w6c8_ew;
    let P20 := fresh "P20p" in
    assert (P20 : getr (ms_regs ms) (20%bv : bv 5) = Z_to_bv 64 0) by
      (rewrite (st_ok_restrict_reg rsegs _ _ _ _ (20%bv : bv 5) HS);
       replace (sr_get (ss_regs ssf) (20%bv : bv 5)) with (SOff 33 (-2)) by (vm_compute; reflexivity);
       cbn [sv_denot]; rewrite H33; f_equal; lia);
    let HP := fresh "HSp" in
    pose proof (st_ok_pin_lit rsegs _ _ _ (20%bv : bv 5) 0 HS eq_refl P20) as HP;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HP; clear HS H33 P20; rename HP into HS
  end.

(* the table region and the input byte's region against a region of the state, by conversion *)
Lemma w6c8_ext_tbl : forall E (rr : YP09.region) tb b2,
  base_val E (YP09.r_base rr) = b2 ->
  (tb + 16 <= b2 + YP09.r_lo rr \/ b2 + YP09.r_hi rr <= tb) ->
  extent_disjoint E (w6c_RT tb) rr.
Proof.
intros E rr tb b2 Hb H. unfold extent_disjoint, w6c_RT.
cbn [YP09.r_base YP09.r_lo YP09.r_hi]. change (base_val E None) with 0.
rewrite Hb, !Z.add_0_l. exact H.
Qed.

Lemma w6c8_ext_ris : forall E (rr : YP09.region) a4 b2,
  bv_unsigned (ew E 14) = a4 -> base_val E (YP09.r_base rr) = b2 ->
  (a4 + 3 <= b2 + YP09.r_lo rr \/ b2 + YP09.r_hi rr <= a4 + 2) ->
  extent_disjoint E w6c_RIs rr.
Proof.
intros E rr a4 b2 H14 Hb H. unfold extent_disjoint, w6c_RIs.
cbn [YP09.r_base YP09.r_lo YP09.r_hi].
change (base_val E (Some 14%nat)) with (bv_unsigned (ew E 14)).
rewrite H14, Hb. exact H.
Qed.


(* a byte of the input is outside the write set of this piece *)
Lemma w6c8_in_out : forall R F cur n a, 0 <= cur -> amem_range cur n ->
  (forall x, cur <= x < cur + n -> ~ (R - T_SEG_STK <= x < R + 0x160) /\ ~ (F + 0x20 <= x < F + 0x158)) ->
  cur <= a < cur + n -> w6c8_out R F a.
Proof.
intros R F cur n a H0 Ham Hdis Ha. destruct (Hdis a Ha) as (H1 & H2).
unfold w6c8_out, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, T_SEG_STK, ASTACK in *.
repeat split; lia.
Qed.

(* the awr obligation of a run of this piece; hfw is the frame's awr_byte fact *)
Ltac w6c8_awr_now hfw :=
  lazymatch goal with
  | |- awr_ok ?Ef ?rs ?stk ?sp ?fp ?b0 ?bc ?lyy ?ow =>
    eapply (w6c8_awr Ef rs stk sp fp b0 bc lyy ow _ _);
    [ w6c8_ew | w6c8_ew | unfold T_SEG_STK, ASTACK in *; lia | lia
    | intros a Ha; apply hfw; lia | vm_compute; reflexivity ]
  end.

(* a table split arm: pin a0 and a1 to the literal address and index of t.9[j], then drop the input
   region and add the table's 16 read-only bytes *)
Ltac w6c8_tbl jj hj p10 p11 :=
  rewrite hj in p10, p11;
  lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
    let HA := fresh "HSa" in
    pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) (W6C_T8 + 4 * jj) HS eq_refl p10) as HA;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HA; clear HS;
    let HB := fresh "HSb" in
    pose proof (st_ok_pin_lit rsegs _ _ _ (11%bv : bv 5) jj HA eq_refl p11) as HB;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HB; clear HA; rename HB into HS
  end;
  lazymatch goal with
  | hrom : rom_view _ ?WW ?mc,
    ke : forall a, w6c8_out ?RR ?FF a -> _,
    dtf : forall a, W6C_T6 <= a < W6C_T8 + 16 -> _,
    HS : st_ok _ ?Ef (mkSS ?pc ?rg [?x1; ?x2; ?x3] ?rv ?f) (restrict _ ?ms) |- _ =>
    assert (U9f : bv_unsigned (ew Ef 9) = RR) by w6c8_ew;
    assert (U32f : bv_unsigned (ew Ef 32) = FF) by w6c8_ew;
    apply (w6c_st_ok_drop Ef pc rg [x1; x2] x3 (@nil YP09.region) rv f) in HS;
    cbn [app] in HS;
    assert (HRT : region_ok rsegs Ef (mrestrict (w_H WW) (ms_mem ms)) (w6c_RT W6C_T8)) by
      (apply (w6c8_RT_keep Ef WW mc (ms_mem ms) W6C_T8);
       [ apply (w6c_RT_ok Ef WW mc W6C_T8 hrom w6c_rom_tbl8 ltac:(unfold W6C_T8; lia)
           ltac:(unfold W6C_T8; lia))
       | intros x Hx; apply ke; pose proof (dtf x ltac:(unfold W6C_T6, W6C_T8 in *; lia)) as Hxx;
         unfold w6c8_out; unfold W6C_T8 in *; try unfold kHighMemBeg in *;
         try unfold T_SEG_STK in *; try unfold ASTACK in *; repeat split; lia ]);
    let HT := fresh "HSt" in
    pose proof (ast_ok_add_region rsegs Ef _ _ (w6c_RT W6C_T8) HS ltac:(vm_compute; reflexivity) HRT
      ltac:(cbn [all_disjoint];
            split;
            [ apply (w6c8_ext_tbl Ef _ W6C_T8 RR);
              [ exact U9f
              | cbn [YP09.r_lo YP09.r_hi]; unfold W6C_T8; try unfold kHighMemBeg in *;
                try unfold T_SEG_STK in *; try unfold ASTACK in *; lia ]
            | split;
              [ apply (w6c8_ext_tbl Ef _ W6C_T8 FF);
                [ exact U32f
                | cbn [YP09.r_lo YP09.r_hi];
                  pose proof (dtf W6C_T8 ltac:(unfold W6C_T6, W6C_T8; lia)) as Hxt;
                  unfold W6C_T8 in *; lia ]
              | exact I ] ])) as HT;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HT; clear HS HRT U9f U32f; rename HT into HS
  end.

(* e's two header words, read off the chunks of the state's e region (the third of the three) *)
(* the size word is a literal, or the engine's AND of the second input byte with 3 *)
Ltac w6c8_szpf :=
  first [ reflexivity
        | apply w6c8_denot_of_U; apply (w6c_U_and3 _ 36 _); [ w6c8_ew | assumption ] ].

Ltac w6c8_hdr FF tyv szv tych szch :=
  lazymatch goal with
  | HS : st_ok _ ?Ef ?ssf (restrict (w_H ?WW) ?ms) |- _ =>
    let rE := eval vm_compute in (nth_error (ss_mem ssf) 2) in
    let rg := lazymatch rE with Some ?x => x end in
    assert (HRE : region_ok rsegs Ef (ms_mem (restrict (w_H WW) ms)) rg)
      by (apply (w6c_region_nth Ef ssf _ 2 rg HS); vm_compute; reflexivity);
    assert (U32h : bv_unsigned (ew Ef 32) = FF) by w6c8_ew;
    assert (Vt : val_mem rsegs (mrestrict (w_H WW) (ms_mem ms)) (FF + 0xf0) 4 tyv)
      by (apply (w6c_field Ef _ 32%nat FF _ _ _ _ _ 0xf0 4 tych tyv HRE U32h ltac:(w6c8_inc));
          [reflexivity | cbn; lia | cbn; lia]);
    assert (Vs : val_mem rsegs (mrestrict (w_H WW) (ms_mem ms)) (FF + 0xf4) 4 szv)
      by (apply (w6c_field Ef _ 32%nat FF _ _ _ _ _ 0xf4 4 szch szv HRE U32h ltac:(w6c8_inc));
          [w6c8_szpf | cbn; lia | cbn; lia]);
    clear HRE U32h
  end.

(* the callee's entry is reached: lib/A/HPgW6cTail.v takes the call and the four instructions after it *)
Ltac w6c8_r12 :=
  lazymatch goal with HSq : st_ok _ ?Ef ?ssf (restrict _ ?ms) |- _ =>
    rewrite (st_ok_restrict_reg rsegs _ _ _ _ (12%bv : bv 5) HSq);
    let e := eval vm_compute in (sr_get (ss_regs ssf) (12%bv : bv 5)) in
    replace (sr_get (ss_regs ssf) (12%bv : bv 5)) with e by (vm_compute; reflexivity)
  end;
  unfold w64; w6c8_szpf.

Ltac w6c8_r20 :=
  lazymatch goal with HSq : st_ok _ ?Ef _ _ |- _ => w6c8_regn HSq (20%bv : bv 5);
    try (let H33 := fresh "H33r" in assert (H33 : bv_unsigned (ew Ef 33) = _) by w6c8_ew;
         rewrite H33; clear H33) end;
  unfold w64; first [ reflexivity | f_equal; lia ].

Ltac w6c8_close hctx hin hjj hae ex :=
  lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
    eapply w6c8_fin;
    [ exact hctx | exact hin | exact HS | reflexivity | reflexivity | exact hjj | w6c8_kio
    | intros rq Hrq;
      lazymatch goal with HSq : st_ok _ ?Ef _ _ |- _ =>
        apply (regs_kept_of_st_ok rsegs Ef _ _ _ ex (w_H _)
          [1; 10; 11; 12; 13; 14; 15; 16; 17; 20; 24; 25]%bv HSq ltac:(env_agree_chain hae)
          ltac:(vm_compute; reflexivity) rq) end;
      [ cbv [w6c_keep In] in Hrq; repeat (destruct Hrq as [<-|Hrq]; [vm_compute; discriminate|]);
        destruct Hrq
      | cbv [w6c_keep In] in Hrq;
        repeat (destruct Hrq as [<-|Hrq];
          [cbv [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]);
        destruct Hrq ]
    | lazymatch goal with HSq : st_ok _ _ _ _ |- _ => w6c8_regn HSq (1%bv : bv 5) end; reflexivity
    | lazymatch goal with HSq : st_ok _ ?Ef _ _ |- _ => w6c8_regn HSq (10%bv : bv 5);
        let H32 := fresh "H32q" in assert (H32 : bv_unsigned (ew Ef 32) = _) by w6c8_ew;
        rewrite H32; clear H32 end;
      unfold w64; f_equal; lia
    | lazymatch goal with HSq : st_ok _ _ _ _ |- _ => w6c8_regn HSq (11%bv : bv 5) end; reflexivity
    | w6c8_r12
    | w6c8_r20
    | lazymatch goal with HSq : st_ok _ ?Ef _ _ |- _ => w6c8_regn HSq (24%bv : bv 5);
        let H14 := fresh "H14q" in assert (H14 : bv_unsigned (ew Ef 14) = _) by w6c8_ew;
        rewrite H14; clear H14 end;
      unfold w64; f_equal; lia
    | lia
    | assumption
    | assumption
    | assumption ]
  end.

(* ---------------- r = [b]: one byte after the kind byte ---------------- *)
Lemma w6c8_one : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa (b : byte),
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa [b] ->
SRr rsegs W (cfg_at rsegs W6C_D8 regs memc mdc)
  (w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
     (fst (w6c_ent 8 [b])) (cur + Z.of_nat (length [b] - length (snd (w6c_ent 8 [b]))))
     (Z.of_nat (length (snd (w6c_ent 8 [b])))) sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa b Hctx Hin.
pose proof Hctx as Hctx0. pose proof Hin as Hin0.
destruct Hctx as (HJ & HG & HROM).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
destruct (w6c_present B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx0) as (HprF & HprR).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HFeq & HFapp & HF32).
destruct Hin as (D2 & D3 & D4 & D9 & D23 & D24 & D14 & D25 & Dm0 & Db0 & Dsa & Dc0 & Df0 & Df8 &
  Dez & Dfsh & Drm & Dra & Dhull & Damr & Dcur1 & Dcur2 & Ddisj & Dt6 & Dt8 & Dtf).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
cbn [length] in D25, Df8, Dcur2, Dra, Dhull, Damr, Ddisj.
pose proof (Cursor.byte_range b) as Hb256.
pose proof (Ddisj cur ltac:(lia)) as Hdc.
pose proof w6c_wx as Hwx. pose proof w6c_segs_low as Hsl. pose proof LAWS as HL.
assert (HAE : env_agree 32 (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0))
  (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0))) by apply env_agree_refl.
assert (U9 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 (9%bv) eq_refl), D9. apply unsigned_lit_small.
  unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia. }
assert (U32 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) 32) = F).
{ rewrite (w6c_e32 regs F 2 (bv_unsigned b) sa 0). apply unsigned_lit_small. lia. }
assert (U23 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) 23) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs _ 23 (23%bv) eq_refl), D23. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (U14 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) 14) = cur - 1).
{ rewrite (ew_Ereg_nat regs _ 14 (14%bv) eq_refl), D14. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) 33) = 2).
{ rewrite (w6c_e33 regs F 2 (bv_unsigned b) sa 0). apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) 32 = w64 F)
  by apply (w6c_e32 regs F 2 (bv_unsigned b) sa 0).
assert (E33 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) 33 = w64 2)
  by apply (w6c_e33 regs F 2 (bv_unsigned b) sa 0).
assert (E34 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) 34 = w64 (bv_unsigned b))
  by apply (w6c_e34 regs F 2 (bv_unsigned b) sa 0).
assert (E35 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) 35 = w64 sa)
  by apply (w6c_e35 regs F 2 (bv_unsigned b) sa 0).
assert (E36 : ew (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) 36 = w64 0)
  by apply (w6c_e36 regs F 2 (bv_unsigned b) sa 0).
destruct (w6c8_hdr0 (w_H W) memc (F + 0xf0) Dez) as (Vz0 & Vz4).
replace (F + 0xf0 + 4) with (F + 0xf4) in Vz4 by lia.
assert (Vb : val_mem rsegs (mrestrict (w_H W) memc) (cur - 1 + 1) 1 (bv_unsigned b)).
{ pose proof (w6c8_byte (w_H W) memc cur [b] 0 Drm ltac:(cbn [length]; lia)) as Hv.
  cbn [nth] in Hv. replace (cur - 1 + 1) with (cur + Z.of_nat 0) by lia. exact Hv. }
assert (HraE : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0xf0) 8).
{ replace (F + 0xf0) with (F + HM_E + 0) by (unfold HM_E; lia).
  apply (hm_A_ra_e rsegs _ _ F false false false false false 0 8);
    [rewrite <- hs_PJ_sh; exact Dfsh | apply w6c_F8; exact HF32 | lia | lia]. }
assert (KE : forall a, w6c8_out R F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
assert (SHOK : sh_ok rsegs w6c_Bx w6c_SH (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0))
  (mrestrict (w_H W) memc)).
{ apply (w6c8_shok_any W (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) memc memc R F U23 U32
    ltac:(lia) ltac:(lia) HFapp ltac:(unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia) HraE KE). }
assert (HS0 : st_ok rsegs (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0))
  (mkSS W6C_D8 sr_atoms [w6c_RS; w6c_RE; w6c_RI 1] None (mkFacts (w6c_facts 2 2 (2 ^ 47 - 3)) [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6C_D8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (w6c_RS_ok (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) W memc R F 2 sa U9 E32 E33 E35);
        [unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia | lia | lia | lia | lia | lia
        | intros o Ho; apply HprR; lia | exact Dm0 | exact Db0 | exact Dc0 | exact Df0 | exact Df8].
    + apply (w6c_RE_ok (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) W memc F U32);
        [lia | lia | intros o Ho; apply HprF; lia | exact Vz0 | exact Vz4].
    + apply (w6c_RI_ok (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) W memc (cur - 1)
        (bv_unsigned b) 0 1 U14 E34 E36);
        [lia | lia | lia | lia | lia | intros _; exact Vb | intros Hx; exfalso; lia].
  - cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint, w6c_RS, w6c_RE, w6c_RI, base_val.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi firstn].
    rewrite U9, U32, U14. unfold T_SEG_STK, ASTACK in *.
    repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
    apply (w6c_facts_ok (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) R F (cur - 1) 2
      (bv_unsigned b) 0 2 2 (2 ^ 47 - 3) U9 U32 U23 U14 U33);
      [rewrite (w6c_e34 regs F 2 (bv_unsigned b) sa 0); apply unsigned_lit_small; lia
      | rewrite (w6c_e36 regs F 2 (bv_unsigned b) sa 0); apply unsigned_lit_small; lia
      | unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia | exact HR16 | lia | exact HF32
      | lia | lia | lia | lia]. }
pose proof (w6c_pin (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) _ _ (24%bv) (SOff 14 1) HS0 eq_refl
  ltac:(cbn [ss_regs]; replace (sr_get sr_atoms (24%bv : bv 5)) with (SOff 24 0) by (vm_compute; reflexivity);
        cbn [sv_denot]; rewrite U14, (ew_Ereg_nat regs _ 24 (24%bv) eq_refl), D24;
        rewrite unsigned_lit_small by lia; f_equal; lia)) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1. clear HS0.
pose proof (w6c_pin (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) _ _ (25%bv) (SOff 33 (-1)) HS1 eq_refl
  ltac:(cbn [ss_regs];
        replace (sr_get (sr_set sr_atoms (24%bv : bv 5) (SOff 14 1)) (25%bv : bv 5)) with (SOff 25 0)
          by (vm_compute; reflexivity);
        cbn [sv_denot]; rewrite U33, (ew_Ereg_nat regs _ 25 (25%bv) eq_refl), D25;
        rewrite unsigned_lit_small by lia; f_equal; lia)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS. clear HS1.
unfold cfg_at. change (w64 W6C_D8) with (Z_to_bv 64 W6C_D8).
assert (Ht4 : 0 <= bv_unsigned b mod 4 < 4) by (apply Z.mod_pos_bound; lia).
aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan 0x81e54.
{ apply (w6c_obl (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) (w_H W) memc _ 4
    (W6C_T8 + 4 * (bv_unsigned b mod 4))).
  - apply (range_addressable_sub _ _ W6C_T8 16); [exact Dt8 | unfold W6C_T8; lia | unfold W6C_T8; lia].
  - rewrite U_SOff, U23, Z.add_0_r. apply zcanon_id. unfold SHADOW_OFF, M64. lia.
  - exact (w6c_U_tbl (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) W6C_T8 (bv_unsigned b) E34 Hb256
      ltac:(unfold W6C_T8; lia)). }
{ apply (w6c_obl (Ereg regs (w6c_extra F 2 (bv_unsigned b) sa 0)) (w_H W) memc (SOff 14 1) 1 cur).
  - apply (range_addressable_sub _ _ cur (Z.of_nat 1)); [exact Dra | lia | lia].
  - rewrite U_SOff, U23, Z.add_0_r. apply zcanon_id. unfold SHADOW_OFF, M64. lia.
  - rewrite U_SOff, U14. replace (cur - 1 + 1) with cur by lia. apply zcanon_id. unfold M64. lia. }
{ w6c8_awr_now HFw. }
w6c8_step KE KE1 R F. w6c8_clean.
lazymatch goal with HS : st_ok _ ?Ef ?ssf (restrict _ ?ms) |- _ =>
  assert (E34f : ew Ef 34 = Z_to_bv 64 (bv_unsigned b)) by
    (change (Z_to_bv 64 (bv_unsigned b)) with (w64 (bv_unsigned b)); w6c8_ew);
  assert (P10 : getr (ms_regs ms) (10%bv : bv 5) = Z_to_bv 64 (W6C_T8 + 4 * (bv_unsigned b mod 4))) by
    (rewrite (st_ok_restrict_reg rsegs _ _ _ _ (10%bv : bv 5) HS);
     replace (sr_get (ss_regs ssf) (10%bv : bv 5))
       with (SAlu ALU_ADD (SLit W6C_T8) (SAlu ALU_SLL (SAlu ALU_AND (SOff 34 0) (SLit 3)) (SLit 2)))
       by (vm_compute; reflexivity);
     apply w6c8_denot_of_U;
     exact (w6c_U_tbl Ef W6C_T8 (bv_unsigned b) E34f Hb256 ltac:(unfold W6C_T8; lia)));
  assert (P11 : getr (ms_regs ms) (11%bv : bv 5) = Z_to_bv 64 (bv_unsigned b mod 4)) by
    (rewrite (st_ok_restrict_reg rsegs _ _ _ _ (11%bv : bv 5) HS);
     replace (sr_get (ss_regs ssf) (11%bv : bv 5)) with (SAlu ALU_AND (SOff 34 0) (SLit 3))
       by (vm_compute; reflexivity);
     apply w6c8_denot_of_U; exact (w6c_U_and3 Ef 34 (bv_unsigned b) E34f Hb256))
end.
assert (Hjc : bv_unsigned b mod 4 = 0 \/ bv_unsigned b mod 4 = 1 \/ bv_unsigned b mod 4 = 2 \/
              bv_unsigned b mod 4 = 3) by lia.
destruct Hjc as [Hj|[Hj|[Hj|Hj]]].
- (* t.9[0] = POD_INT *)
  assert (Hed : fst (w6c_ent 8 [b]) = Ent 4 0 (zeros (Z.to_nat 0)))
    by (rewrite (w6c8_e1 b 0 Hj ltac:(lia)); cbn [fst]; rewrite w6c8_t8_0; reflexivity).
  assert (Hcc : cur + Z.of_nat (length [b] - length (snd (w6c_ent 8 [b]))) = cur + 1)
    by (rewrite (w6c8_e1 b 0 Hj ltac:(lia)); cbn [snd length Nat.sub]; lia).
  assert (Hnn : Z.of_nat (length (snd (w6c_ent 8 [b]))) = 0)
    by (rewrite (w6c8_e1 b 0 Hj ltac:(lia)); cbn [snd length]; lia).
  rewrite Hed, Hcc, Hnn. clear Hed Hcc Hnn.
  w6c8_tbl 0 Hj P10 P11.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET.
  { w6c8_awr_now HFw. }
  w6c8_step KE1 KE2 R F. w6c8_clean.
  w6c8_pin20.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET.
  { w6c8_awr_now HFw. }
  w6c8_step KE2 KE3 R F. w6c8_clean.
  w6c8_hdr F 4 0 (SLit 4) (SLit 0).
  w6c8_close Hctx0 Hin0 HJ HAE (w6c_extra F 2 (bv_unsigned b) sa 0).
- (* t.9[1] = POD_FLOAT *)
  assert (Hed : fst (w6c_ent 8 [b]) = Ent 6 0 (zeros (Z.to_nat 0)))
    by (rewrite (w6c8_e1 b 1 Hj ltac:(lia)); cbn [fst]; rewrite w6c8_t8_1; reflexivity).
  assert (Hcc : cur + Z.of_nat (length [b] - length (snd (w6c_ent 8 [b]))) = cur + 1)
    by (rewrite (w6c8_e1 b 1 Hj ltac:(lia)); cbn [snd length Nat.sub]; lia).
  assert (Hnn : Z.of_nat (length (snd (w6c_ent 8 [b]))) = 0)
    by (rewrite (w6c8_e1 b 1 Hj ltac:(lia)); cbn [snd length]; lia).
  rewrite Hed, Hcc, Hnn. clear Hed Hcc Hnn.
  w6c8_tbl 1 Hj P10 P11.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET.
  { w6c8_awr_now HFw. }
  w6c8_step KE1 KE2 R F. w6c8_clean.
  w6c8_pin20.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET.
  { w6c8_awr_now HFw. }
  w6c8_step KE2 KE3 R F. w6c8_clean.
  w6c8_hdr F 6 0 (SLit 6) (SLit 0).
  w6c8_close Hctx0 Hin0 HJ HAE (w6c_extra F 2 (bv_unsigned b) sa 0).
- (* t.9[2] = POD_BOOL *)
  assert (Hed : fst (w6c_ent 8 [b]) = Ent 2 0 (zeros (Z.to_nat 0)))
    by (rewrite (w6c8_e1 b 2 Hj ltac:(lia)); cbn [fst]; rewrite w6c8_t8_2; reflexivity).
  assert (Hcc : cur + Z.of_nat (length [b] - length (snd (w6c_ent 8 [b]))) = cur + 1)
    by (rewrite (w6c8_e1 b 2 Hj ltac:(lia)); cbn [snd length Nat.sub]; lia).
  assert (Hnn : Z.of_nat (length (snd (w6c_ent 8 [b]))) = 0)
    by (rewrite (w6c8_e1 b 2 Hj ltac:(lia)); cbn [snd length]; lia).
  rewrite Hed, Hcc, Hnn. clear Hed Hcc Hnn.
  w6c8_tbl 2 Hj P10 P11.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET.
  { w6c8_awr_now HFw. }
  w6c8_step KE1 KE2 R F. w6c8_clean.
  w6c8_pin20.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET.
  { w6c8_awr_now HFw. }
  w6c8_step KE2 KE3 R F. w6c8_clean.
  w6c8_hdr F 2 0 (SLit 2) (SLit 0).
  w6c8_close Hctx0 Hin0 HJ HAE (w6c_extra F 2 (bv_unsigned b) sa 0).
- (* t.9[3] = POD_STRING: `beq a1,3` is taken and the pod is empty *)
  assert (Hed : fst (w6c_ent 8 [b]) = Ent 8 0 (zeros (Z.to_nat 0)))
    by (rewrite (w6c8_e1 b 3 Hj ltac:(lia)); cbn [fst]; rewrite w6c8_t8_3; reflexivity).
  assert (Hcc : cur + Z.of_nat (length [b] - length (snd (w6c_ent 8 [b]))) = cur + 1)
    by (rewrite (w6c8_e1 b 3 Hj ltac:(lia)); cbn [snd length Nat.sub]; lia).
  assert (Hnn : Z.of_nat (length (snd (w6c_ent 8 [b]))) = 0)
    by (rewrite (w6c8_e1 b 3 Hj ltac:(lia)); cbn [snd length]; lia).
  rewrite Hed, Hcc, Hnn. clear Hed Hcc Hnn.
  w6c8_tbl 3 Hj P10 P11.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET.
  { w6c8_awr_now HFw. }
  w6c8_step KE1 KE2 R F. w6c8_clean.
  w6c8_hdr F 8 0 (SLit 8) (SLit 0).
  w6c8_close Hctx0 Hin0 HJ HAE (w6c_extra F 2 (bv_unsigned b) sa 0).
Qed.

(* ---------------- r = b :: s :: r2: at least two bytes after the kind byte ---------------- *)
Lemma w6c8_two : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa
  (b s' : byte) (r2 : list byte),
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in_D B W memc regs R F cur sa (b :: s' :: r2) ->
SRr rsegs W (cfg_at rsegs W6C_D8 regs memc mdc)
  (w6c_jpost B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F
     (fst (w6c_ent 8 (b :: s' :: r2)))
     (cur + Z.of_nat (length (b :: s' :: r2) - length (snd (w6c_ent 8 (b :: s' :: r2)))))
     (Z.of_nat (length (snd (w6c_ent 8 (b :: s' :: r2))))) sa).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa b s' r2 Hctx Hin.
pose proof Hctx as Hctx0. pose proof Hin as Hin0.
destruct Hctx as (HJ & HG & HROM).
destruct (w6c_frame B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos HJ HG)
  as (HFc & HF4 & HF47 & HRc & Hsp16 & Hsp47 & HFS & HFw).
destruct (w6c_present B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx0) as (HprF & HprR).
pose proof HG as (HR16 & HSTK & HRS & HRk & Hown & HFeq & HFapp & HF32).
destruct Hin as (D2 & D3 & D4 & D9 & D23 & D24 & D14 & D25 & Dm0 & Db0 & Dsa & Dc0 & Df0 & Df8 &
  Dez & Dfsh & Drm & Dra & Dhull & Damr & Dcur1 & Dcur2 & Ddisj & Dt6 & Dt8 & Dtf).
pose proof alloc_ceiling_value as (Hc1 & _). pose proof alloc_ceiling_lt as Hc2.
assert (Hlen2 : Z.of_nat (length (b :: s' :: r2)) = Z.of_nat (length r2) + 2) by (cbn [length]; lia).
pose proof (Cursor.byte_range b) as Hb256.
pose proof (Cursor.byte_range s') as Hs256.
assert (Hs4 : 0 <= bv_unsigned s' mod 4 < 4) by (apply Z.mod_pos_bound; lia).
pose proof (Ddisj cur ltac:(lia)) as Hdc.
pose proof w6c_wx as Hwx. pose proof w6c_segs_low as Hsl. pose proof LAWS as HL.
assert (HAE : env_agree 32
  (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1) (bv_unsigned b) sa (bv_unsigned s')))
  (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1) (bv_unsigned b) sa (bv_unsigned s'))))
  by apply env_agree_refl.
assert (U9 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1)
  (bv_unsigned b) sa (bv_unsigned s'))) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 (9%bv) eq_refl), D9. apply unsigned_lit_small.
  unfold kHighMemBeg, T_SEG_STK, ASTACK in *. lia. }
assert (U32 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1)
  (bv_unsigned b) sa (bv_unsigned s'))) 32) = F).
{ rewrite (w6c_e32 regs F _ (bv_unsigned b) sa (bv_unsigned s')). apply unsigned_lit_small. lia. }
assert (U23 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1)
  (bv_unsigned b) sa (bv_unsigned s'))) 23) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs _ 23 (23%bv) eq_refl), D23. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (U14 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1)
  (bv_unsigned b) sa (bv_unsigned s'))) 14) = cur - 1).
{ rewrite (ew_Ereg_nat regs _ 14 (14%bv) eq_refl), D14. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1)
  (bv_unsigned b) sa (bv_unsigned s'))) 33) = Z.of_nat (length (b :: s' :: r2)) + 1).
{ rewrite (w6c_e33 regs F _ (bv_unsigned b) sa (bv_unsigned s')). apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1)
  (bv_unsigned b) sa (bv_unsigned s'))) 32 = w64 F)
  by apply (w6c_e32 regs F _ (bv_unsigned b) sa (bv_unsigned s')).
assert (E33 : ew (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1)
  (bv_unsigned b) sa (bv_unsigned s'))) 33 = w64 (Z.of_nat (length (b :: s' :: r2)) + 1))
  by apply (w6c_e33 regs F _ (bv_unsigned b) sa (bv_unsigned s')).
assert (E34 : ew (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1)
  (bv_unsigned b) sa (bv_unsigned s'))) 34 = w64 (bv_unsigned b))
  by apply (w6c_e34 regs F _ (bv_unsigned b) sa (bv_unsigned s')).
assert (E35 : ew (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1)
  (bv_unsigned b) sa (bv_unsigned s'))) 35 = w64 sa)
  by apply (w6c_e35 regs F _ (bv_unsigned b) sa (bv_unsigned s')).
assert (E36 : ew (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1)
  (bv_unsigned b) sa (bv_unsigned s'))) 36 = w64 (bv_unsigned s'))
  by apply (w6c_e36 regs F _ (bv_unsigned b) sa (bv_unsigned s')).
destruct (w6c8_hdr0 (w_H W) memc (F + 0xf0) Dez) as (Vz0 & Vz4).
replace (F + 0xf0 + 4) with (F + 0xf4) in Vz4 by lia.
assert (Vb : val_mem rsegs (mrestrict (w_H W) memc) (cur - 1 + 1) 1 (bv_unsigned b)).
{ pose proof (w6c8_byte (w_H W) memc cur (b :: s' :: r2) 0 Drm ltac:(cbn [length]; lia)) as Hv.
  cbn [nth] in Hv. replace (cur - 1 + 1) with (cur + Z.of_nat 0) by lia. exact Hv. }
assert (Vs2 : val_mem rsegs (mrestrict (w_H W) memc) (cur - 1 + 2) 1 (bv_unsigned s')).
{ pose proof (w6c8_byte (w_H W) memc cur (b :: s' :: r2) 1 Drm ltac:(cbn [length]; lia)) as Hv.
  cbn [nth] in Hv. replace (cur - 1 + 2) with (cur + Z.of_nat 1) by lia. exact Hv. }
assert (HraE : range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0xf0) 8).
{ replace (F + 0xf0) with (F + HM_E + 0) by (unfold HM_E; lia).
  apply (hm_A_ra_e rsegs _ _ F false false false false false 0 8);
    [rewrite <- hs_PJ_sh; exact Dfsh | apply w6c_F8; exact HF32 | lia | lia]. }
assert (KE : forall a, w6c8_out R F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
assert (SHOK : sh_ok rsegs w6c_Bx w6c_SH (Ereg regs (w6c_extra F
  (Z.of_nat (length (b :: s' :: r2)) + 1) (bv_unsigned b) sa (bv_unsigned s'))) (mrestrict (w_H W) memc)).
{ apply (w6c8_shok_any W _ memc memc R F U23 U32 ltac:(lia) ltac:(lia) HFapp
    ltac:(unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia) HraE KE). }
assert (HS0 : st_ok rsegs (Ereg regs (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1)
    (bv_unsigned b) sa (bv_unsigned s')))
  (mkSS W6C_D8 sr_atoms [w6c_RS; w6c_RE; w6c_RI 2] None
     (mkFacts (w6c_facts 3 (2 ^ 47) (2 ^ 47 - 4)) [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6C_D8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (w6c_RS_ok _ W memc R F (Z.of_nat (length (b :: s' :: r2)) + 1) sa U9 E32 E33 E35);
        [unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia | lia | lia | lia | lia | lia
        | intros o Ho; apply HprR; lia | exact Dm0 | exact Db0 | exact Dc0 | exact Df0 | exact Df8].
    + apply (w6c_RE_ok _ W memc F U32);
        [lia | lia | intros o Ho; apply HprF; lia | exact Vz0 | exact Vz4].
    + apply (w6c_RI_ok _ W memc (cur - 1) (bv_unsigned b) (bv_unsigned s') 2 U14 E34 E36);
        [lia | lia | lia | lia | lia | intros _; exact Vb | intros _; exact Vs2].
  - cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint, w6c_RS, w6c_RE, w6c_RI, base_val.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi firstn].
    rewrite U9, U32, U14. unfold T_SEG_STK, ASTACK in *.
    repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
    apply (w6c_facts_ok _ R F (cur - 1) (Z.of_nat (length (b :: s' :: r2)) + 1)
      (bv_unsigned b) (bv_unsigned s') 3 (2 ^ 47) (2 ^ 47 - 4) U9 U32 U23 U14 U33);
      [rewrite (w6c_e34 regs F _ (bv_unsigned b) sa (bv_unsigned s')); apply unsigned_lit_small; lia
      | rewrite (w6c_e36 regs F _ (bv_unsigned b) sa (bv_unsigned s')); apply unsigned_lit_small; lia
      | unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia | exact HR16 | lia | exact HF32
      | lia | lia | lia | lia]. }
pose proof (w6c_pin _ _ _ (24%bv) (SOff 14 1) HS0 eq_refl
  ltac:(cbn [ss_regs]; replace (sr_get sr_atoms (24%bv : bv 5)) with (SOff 24 0) by (vm_compute; reflexivity);
        cbn [sv_denot]; rewrite U14, (ew_Ereg_nat regs _ 24 (24%bv) eq_refl), D24;
        rewrite unsigned_lit_small by lia; f_equal; lia)) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1. clear HS0.
pose proof (w6c_pin _ _ _ (25%bv) (SOff 33 (-1)) HS1 eq_refl
  ltac:(cbn [ss_regs];
        replace (sr_get (sr_set sr_atoms (24%bv : bv 5) (SOff 14 1)) (25%bv : bv 5)) with (SOff 25 0)
          by (vm_compute; reflexivity);
        cbn [sv_denot]; rewrite U33, (ew_Ereg_nat regs _ 25 (25%bv) eq_refl), D25;
        rewrite unsigned_lit_small by lia; f_equal; lia)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS. clear HS1.
unfold cfg_at. change (w64 W6C_D8) with (Z_to_bv 64 W6C_D8).
assert (Ht4 : 0 <= bv_unsigned b mod 4 < 4) by (apply Z.mod_pos_bound; lia).
aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan 0x81e54.
{ apply (w6c_obl _ (w_H W) memc _ 4 (W6C_T8 + 4 * (bv_unsigned b mod 4))).
  - apply (range_addressable_sub _ _ W6C_T8 16); [exact Dt8 | unfold W6C_T8; lia | unfold W6C_T8; lia].
  - rewrite U_SOff, U23, Z.add_0_r. apply zcanon_id. unfold SHADOW_OFF, M64. lia.
  - exact (w6c_U_tbl _ W6C_T8 (bv_unsigned b) E34 Hb256 ltac:(unfold W6C_T8; lia)). }
{ apply (w6c_obl _ (w_H W) memc (SOff 14 1) 1 cur).
  - apply (range_addressable_sub _ _ cur (Z.of_nat (length (b :: s' :: r2)))); [exact Dra | lia | lia].
  - rewrite U_SOff, U23, Z.add_0_r. apply zcanon_id. unfold SHADOW_OFF, M64. lia.
  - rewrite U_SOff, U14. replace (cur - 1 + 1) with cur by lia. apply zcanon_id. unfold M64. lia. }
{ w6c8_awr_now HFw. }
w6c8_step KE KE1 R F. w6c8_clean.
lazymatch goal with HS : st_ok _ ?Ef ?ssf (restrict _ ?ms) |- _ =>
  assert (E34f : ew Ef 34 = Z_to_bv 64 (bv_unsigned b)) by
    (change (Z_to_bv 64 (bv_unsigned b)) with (w64 (bv_unsigned b)); w6c8_ew);
  assert (P10 : getr (ms_regs ms) (10%bv : bv 5) = Z_to_bv 64 (W6C_T8 + 4 * (bv_unsigned b mod 4))) by
    (rewrite (st_ok_restrict_reg rsegs _ _ _ _ (10%bv : bv 5) HS);
     replace (sr_get (ss_regs ssf) (10%bv : bv 5))
       with (SAlu ALU_ADD (SLit W6C_T8) (SAlu ALU_SLL (SAlu ALU_AND (SOff 34 0) (SLit 3)) (SLit 2)))
       by (vm_compute; reflexivity);
     apply w6c8_denot_of_U;
     exact (w6c_U_tbl Ef W6C_T8 (bv_unsigned b) E34f Hb256 ltac:(unfold W6C_T8; lia)));
  assert (P11 : getr (ms_regs ms) (11%bv : bv 5) = Z_to_bv 64 (bv_unsigned b mod 4)) by
    (rewrite (st_ok_restrict_reg rsegs _ _ _ _ (11%bv : bv 5) HS);
     replace (sr_get (ss_regs ssf) (11%bv : bv 5)) with (SAlu ALU_AND (SOff 34 0) (SLit 3))
       by (vm_compute; reflexivity);
     apply w6c8_denot_of_U; exact (w6c_U_and3 Ef 34 (bv_unsigned b) E34f Hb256))
end.
assert (Hjc : bv_unsigned b mod 4 = 0 \/ bv_unsigned b mod 4 = 1 \/ bv_unsigned b mod 4 = 2 \/
              bv_unsigned b mod 4 = 3) by lia.
destruct Hjc as [Hj|[Hj|[Hj|Hj]]].
- (* t.9[0] = 4 *)
  assert (Hed : fst (w6c_ent 8 (b :: s' :: r2)) =
    Ent 4 (bv_unsigned s' mod 4) (zeros (Z.to_nat (bv_unsigned s' mod 4))))
    by (rewrite (w6c8_e2 b s' r2 0 Hj ltac:(lia) ltac:(lia)); cbn [fst]; rewrite w6c8_t8_0; reflexivity).
  assert (Hcc : cur + Z.of_nat (length (b :: s' :: r2) - length (snd (w6c_ent 8 (b :: s' :: r2))))
    = cur + 2) by (rewrite (w6c8_e2 b s' r2 0 Hj ltac:(lia) ltac:(lia)); cbn [snd length Nat.sub]; lia).
  assert (Hnn : Z.of_nat (length (snd (w6c_ent 8 (b :: s' :: r2)))) = Z.of_nat (length r2))
    by (rewrite (w6c8_e2 b s' r2 0 Hj ltac:(lia) ltac:(lia)); cbn [snd]; reflexivity).
  rewrite Hed, Hcc, Hnn. clear Hed Hcc Hnn.
  w6c8_tbl 0 Hj P10 P11.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan 0x81e7c.
  { w6c8_awr_now HFw. }
  w6c8_step KE1 KE2 R F. w6c8_clean.
  (* the table is read: swap it for the second input byte *)
  lazymatch goal with HS : st_ok _ ?Ef (mkSS ?pc ?rg [?x1; ?x2; ?x3] ?rv ?f) (restrict _ ?ms) |- _ =>
    assert (U9g : bv_unsigned (ew Ef 9) = R) by w6c8_ew;
    assert (U32g : bv_unsigned (ew Ef 32) = F) by w6c8_ew;
    assert (U14g : bv_unsigned (ew Ef 14) = cur - 1) by w6c8_ew;
    assert (U23g : bv_unsigned (ew Ef 23) = SHADOW_OFF) by w6c8_ew;
    assert (E36g : ew Ef 36 = w64 (bv_unsigned s')) by w6c8_ew;
    apply (w6c_st_ok_drop Ef pc rg (@nil YP09.region) x1 [x2; x3] rv f) in HS;
    cbn [app] in HS;
    assert (HRI : region_ok rsegs Ef (mrestrict (w_H W) (ms_mem ms)) w6c_RIs) by
      (apply (w6c_RIs_ok Ef W (ms_mem ms) (cur - 1) (bv_unsigned s') U14g E36g ltac:(lia) ltac:(lia)
         Hs256);
       apply (w6c_val_kept (w_H W) memc (w_H W) (ms_mem ms)); [exact Vs2|];
       intros i Hi; apply KE2;
       apply (w6c8_in_out R F cur (Z.of_nat (length (b :: s' :: r2))) (cur - 1 + 2 + i)
         ltac:(lia) Damr Ddisj ltac:(lia)));
    pose proof (ast_ok_add_region rsegs Ef _ _ w6c_RIs HS ltac:(vm_compute; reflexivity) HRI
      ltac:(cbn [all_disjoint];
            split;
            [ apply (w6c8_ext_ris Ef _ (cur - 1) R);
              [ exact U14g | exact U9g
              | cbn [YP09.r_lo YP09.r_hi]; unfold T_SEG_STK, ASTACK in *; lia ]
            | split;
              [ apply (w6c8_ext_ris Ef _ (cur - 1) F);
                [ exact U14g | exact U32g | cbn [YP09.r_lo YP09.r_hi]; lia ]
              | exact I ] ])) as HSr;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSr; clear HS HRI; rename HSr into HS;
    aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET;
    [ apply (w6c_obl Ef (w_H W) (ms_mem ms) (SOff 14 2) 1 (cur + 1));
      [ apply (w6c8_ra_keep W memc (ms_mem ms) R F (cur + 1) 1);
        [ apply (range_addressable_sub _ _ cur (Z.of_nat (length (b :: s' :: r2))));
          [exact Dra | lia | lia]
        | exact KE2
        | intros x Hx; apply w6c8_sh_out;
          [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia | exact HFapp
          | unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia] ]
      | rewrite U_SOff, U23g, Z.add_0_r; apply zcanon_id; unfold SHADOW_OFF, M64; lia
      | rewrite U_SOff, U14g; replace (cur - 1 + 2) with (cur + 1) by lia; apply zcanon_id;
        unfold M64; lia ]
    | w6c8_awr_now HFw
    | ]
  end.
  w6c8_step KE2 KE3 R F. w6c8_clean.
  w6c8_hdr F 4 (bv_unsigned s' mod 4) (SLit 4) (SAlu ALU_AND (SOff 36 0) (SLit 3)).
  w6c8_close Hctx0 Hin0 HJ HAE
    (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1) (bv_unsigned b) sa (bv_unsigned s')).
- (* t.9[1] = 6 *)
  assert (Hed : fst (w6c_ent 8 (b :: s' :: r2)) =
    Ent 6 (bv_unsigned s' mod 4) (zeros (Z.to_nat (bv_unsigned s' mod 4))))
    by (rewrite (w6c8_e2 b s' r2 1 Hj ltac:(lia) ltac:(lia)); cbn [fst]; rewrite w6c8_t8_1; reflexivity).
  assert (Hcc : cur + Z.of_nat (length (b :: s' :: r2) - length (snd (w6c_ent 8 (b :: s' :: r2))))
    = cur + 2) by (rewrite (w6c8_e2 b s' r2 1 Hj ltac:(lia) ltac:(lia)); cbn [snd length Nat.sub]; lia).
  assert (Hnn : Z.of_nat (length (snd (w6c_ent 8 (b :: s' :: r2)))) = Z.of_nat (length r2))
    by (rewrite (w6c8_e2 b s' r2 1 Hj ltac:(lia) ltac:(lia)); cbn [snd]; reflexivity).
  rewrite Hed, Hcc, Hnn. clear Hed Hcc Hnn.
  w6c8_tbl 1 Hj P10 P11.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan 0x81e7c.
  { w6c8_awr_now HFw. }
  w6c8_step KE1 KE2 R F. w6c8_clean.
  (* the table is read: swap it for the second input byte *)
  lazymatch goal with HS : st_ok _ ?Ef (mkSS ?pc ?rg [?x1; ?x2; ?x3] ?rv ?f) (restrict _ ?ms) |- _ =>
    assert (U9g : bv_unsigned (ew Ef 9) = R) by w6c8_ew;
    assert (U32g : bv_unsigned (ew Ef 32) = F) by w6c8_ew;
    assert (U14g : bv_unsigned (ew Ef 14) = cur - 1) by w6c8_ew;
    assert (U23g : bv_unsigned (ew Ef 23) = SHADOW_OFF) by w6c8_ew;
    assert (E36g : ew Ef 36 = w64 (bv_unsigned s')) by w6c8_ew;
    apply (w6c_st_ok_drop Ef pc rg (@nil YP09.region) x1 [x2; x3] rv f) in HS;
    cbn [app] in HS;
    assert (HRI : region_ok rsegs Ef (mrestrict (w_H W) (ms_mem ms)) w6c_RIs) by
      (apply (w6c_RIs_ok Ef W (ms_mem ms) (cur - 1) (bv_unsigned s') U14g E36g ltac:(lia) ltac:(lia)
         Hs256);
       apply (w6c_val_kept (w_H W) memc (w_H W) (ms_mem ms)); [exact Vs2|];
       intros i Hi; apply KE2;
       apply (w6c8_in_out R F cur (Z.of_nat (length (b :: s' :: r2))) (cur - 1 + 2 + i)
         ltac:(lia) Damr Ddisj ltac:(lia)));
    pose proof (ast_ok_add_region rsegs Ef _ _ w6c_RIs HS ltac:(vm_compute; reflexivity) HRI
      ltac:(cbn [all_disjoint];
            split;
            [ apply (w6c8_ext_ris Ef _ (cur - 1) R);
              [ exact U14g | exact U9g
              | cbn [YP09.r_lo YP09.r_hi]; unfold T_SEG_STK, ASTACK in *; lia ]
            | split;
              [ apply (w6c8_ext_ris Ef _ (cur - 1) F);
                [ exact U14g | exact U32g | cbn [YP09.r_lo YP09.r_hi]; lia ]
              | exact I ] ])) as HSr;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSr; clear HS HRI; rename HSr into HS;
    aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET;
    [ apply (w6c_obl Ef (w_H W) (ms_mem ms) (SOff 14 2) 1 (cur + 1));
      [ apply (w6c8_ra_keep W memc (ms_mem ms) R F (cur + 1) 1);
        [ apply (range_addressable_sub _ _ cur (Z.of_nat (length (b :: s' :: r2))));
          [exact Dra | lia | lia]
        | exact KE2
        | intros x Hx; apply w6c8_sh_out;
          [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia | exact HFapp
          | unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia] ]
      | rewrite U_SOff, U23g, Z.add_0_r; apply zcanon_id; unfold SHADOW_OFF, M64; lia
      | rewrite U_SOff, U14g; replace (cur - 1 + 2) with (cur + 1) by lia; apply zcanon_id;
        unfold M64; lia ]
    | w6c8_awr_now HFw
    | ]
  end.
  w6c8_step KE2 KE3 R F. w6c8_clean.
  w6c8_hdr F 6 (bv_unsigned s' mod 4) (SLit 6) (SAlu ALU_AND (SOff 36 0) (SLit 3)).
  w6c8_close Hctx0 Hin0 HJ HAE
    (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1) (bv_unsigned b) sa (bv_unsigned s')).
- (* t.9[2] = 2 *)
  assert (Hed : fst (w6c_ent 8 (b :: s' :: r2)) =
    Ent 2 (bv_unsigned s' mod 4) (zeros (Z.to_nat (bv_unsigned s' mod 4))))
    by (rewrite (w6c8_e2 b s' r2 2 Hj ltac:(lia) ltac:(lia)); cbn [fst]; rewrite w6c8_t8_2; reflexivity).
  assert (Hcc : cur + Z.of_nat (length (b :: s' :: r2) - length (snd (w6c_ent 8 (b :: s' :: r2))))
    = cur + 2) by (rewrite (w6c8_e2 b s' r2 2 Hj ltac:(lia) ltac:(lia)); cbn [snd length Nat.sub]; lia).
  assert (Hnn : Z.of_nat (length (snd (w6c_ent 8 (b :: s' :: r2)))) = Z.of_nat (length r2))
    by (rewrite (w6c8_e2 b s' r2 2 Hj ltac:(lia) ltac:(lia)); cbn [snd]; reflexivity).
  rewrite Hed, Hcc, Hnn. clear Hed Hcc Hnn.
  w6c8_tbl 2 Hj P10 P11.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan 0x81e7c.
  { w6c8_awr_now HFw. }
  w6c8_step KE1 KE2 R F. w6c8_clean.
  (* the table is read: swap it for the second input byte *)
  lazymatch goal with HS : st_ok _ ?Ef (mkSS ?pc ?rg [?x1; ?x2; ?x3] ?rv ?f) (restrict _ ?ms) |- _ =>
    assert (U9g : bv_unsigned (ew Ef 9) = R) by w6c8_ew;
    assert (U32g : bv_unsigned (ew Ef 32) = F) by w6c8_ew;
    assert (U14g : bv_unsigned (ew Ef 14) = cur - 1) by w6c8_ew;
    assert (U23g : bv_unsigned (ew Ef 23) = SHADOW_OFF) by w6c8_ew;
    assert (E36g : ew Ef 36 = w64 (bv_unsigned s')) by w6c8_ew;
    apply (w6c_st_ok_drop Ef pc rg (@nil YP09.region) x1 [x2; x3] rv f) in HS;
    cbn [app] in HS;
    assert (HRI : region_ok rsegs Ef (mrestrict (w_H W) (ms_mem ms)) w6c_RIs) by
      (apply (w6c_RIs_ok Ef W (ms_mem ms) (cur - 1) (bv_unsigned s') U14g E36g ltac:(lia) ltac:(lia)
         Hs256);
       apply (w6c_val_kept (w_H W) memc (w_H W) (ms_mem ms)); [exact Vs2|];
       intros i Hi; apply KE2;
       apply (w6c8_in_out R F cur (Z.of_nat (length (b :: s' :: r2))) (cur - 1 + 2 + i)
         ltac:(lia) Damr Ddisj ltac:(lia)));
    pose proof (ast_ok_add_region rsegs Ef _ _ w6c_RIs HS ltac:(vm_compute; reflexivity) HRI
      ltac:(cbn [all_disjoint];
            split;
            [ apply (w6c8_ext_ris Ef _ (cur - 1) R);
              [ exact U14g | exact U9g
              | cbn [YP09.r_lo YP09.r_hi]; unfold T_SEG_STK, ASTACK in *; lia ]
            | split;
              [ apply (w6c8_ext_ris Ef _ (cur - 1) F);
                [ exact U14g | exact U32g | cbn [YP09.r_lo YP09.r_hi]; lia ]
              | exact I ] ])) as HSr;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSr; clear HS HRI; rename HSr into HS;
    aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET;
    [ apply (w6c_obl Ef (w_H W) (ms_mem ms) (SOff 14 2) 1 (cur + 1));
      [ apply (w6c8_ra_keep W memc (ms_mem ms) R F (cur + 1) 1);
        [ apply (range_addressable_sub _ _ cur (Z.of_nat (length (b :: s' :: r2))));
          [exact Dra | lia | lia]
        | exact KE2
        | intros x Hx; apply w6c8_sh_out;
          [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia | exact HFapp
          | unfold kHighMemBeg, T_SEG_STK, ASTACK in *; lia] ]
      | rewrite U_SOff, U23g, Z.add_0_r; apply zcanon_id; unfold SHADOW_OFF, M64; lia
      | rewrite U_SOff, U14g; replace (cur - 1 + 2) with (cur + 1) by lia; apply zcanon_id;
        unfold M64; lia ]
    | w6c8_awr_now HFw
    | ]
  end.
  w6c8_step KE2 KE3 R F. w6c8_clean.
  w6c8_hdr F 2 (bv_unsigned s' mod 4) (SLit 2) (SAlu ALU_AND (SOff 36 0) (SLit 3)).
  w6c8_close Hctx0 Hin0 HJ HAE
    (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1) (bv_unsigned b) sa (bv_unsigned s')).
- (* t.9[3] = POD_STRING: the second byte is not read *)
  assert (Hed : fst (w6c_ent 8 (b :: s' :: r2)) = Ent 8 0 (zeros (Z.to_nat 0)))
    by (rewrite (w6c8_e3 b s' r2 Hj); cbn [fst]; reflexivity).
  assert (Hcc : cur + Z.of_nat (length (b :: s' :: r2) - length (snd (w6c_ent 8 (b :: s' :: r2))))
    = cur + 1) by (rewrite (w6c8_e3 b s' r2 Hj); cbn [snd length Nat.sub]; lia).
  assert (Hnn : Z.of_nat (length (snd (w6c_ent 8 (b :: s' :: r2)))) = Z.of_nat (length r2) + 1)
    by (rewrite (w6c8_e3 b s' r2 Hj); cbn [snd length]; lia).
  rewrite Hed, Hcc, Hnn. clear Hed Hcc Hnn.
  w6c8_tbl 3 Hj P10 P11.
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_SET.
  { w6c8_awr_now HFw. }
  w6c8_step KE1 KE2 R F. w6c8_clean.
  w6c8_hdr F 8 0 (SLit 8) (SLit 0).
  w6c8_close Hctx0 Hin0 HJ HAE
    (w6c_extra F (Z.of_nat (length (b :: s' :: r2)) + 1) (bv_unsigned b) sa (bv_unsigned s')).
Qed.

(* ======================= the block statement ======================= *)
Theorem w6c_case8 : w6c_case8_stmt B.
Proof.
unfold w6c_case8_stmt, w6c_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa r Hctx Hin.
change (w6c_pc 8) with W6C_D8.
destruct r as [|b [|s' r2]].
- exact (w6c8_nil STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa Hctx Hin).
- exact (w6c8_one STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa b Hctx Hin).
- exact (w6c8_two STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur sa b s' r2
    Hctx Hin).
Qed.

End d.
End c.

Print Assumptions w6c_case8.
