(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6c6.v at cb9cdc023f20; ported to the same
   unit's image B (fuzz_rate.asan-ubsan): image B's pcs, registers and real-frame cells; the pod is e62 (F + 0x210) in
   the class-4 side-stack frame; the no-byte arm reads the table too, so both arms carry the table and its shadow
   granules (a zero shadow region) and the split t & 3 = j sits before the table's check; the three UBSan trap
   branches (two decided by the engine from atom facts, one split and refuted). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the block lemma w6cb_h6 of
   lib/AU/RtPgW6cBaseB.v, the head of case 6 of ent_build's `switch (kind % 10)` (pod.h:340-348) inside
   LLVMFuzzerTestOneInput (0x8076c), from the case entry 0x819a0 to the entry of __asan_memcpy 0x518b8.
   Proves no function (kind: segment lemma).

   THE CODE (registers as in RtPgW6cBaseB.v: s1 = R, s4 = SHADOW_OFF, s2 = c, s6 = |r|, s10 = c - 1, t1 = |r| + 1,
   a6 = 1; every `j 0x83098` is a UBSan trap branch to the `unimp`):
     0x819a0  beqz s6 -> 0x81cf0                      no byte left
     0x819a4  a0 := s2 + 1; 0x819a8 bltu a6,a0 (else the trap)       pointer overflow of c + 1
     0x819b0 .. 0x819bc  the check of s2 (NE-SLOW, slow block 0x822e0)
     0x819c0  lbu a2,0(s2) (= t); a0 := 0x211c0; a2 := t & 3; a3 := 4 (t & 3)
     0x819d4  a1 := ~a0; 0x819d8 bgeu a1,a3 (else the trap)         pointer overflow of the table index
     0x819e0  a1 := t1 - 2 (= |r1|); s2 := s10 + 2; a0 := a0 + a3; j 0x81d00
     0x81cf0  (no byte) a1 := 0; a2 := 0; a0 := 0x211c0
     0x81d00 .. 0x81d10  the check of a0, 4 bytes (NE-SLOW, slow block 0x82250), `ld s6,0x150(s1)` (= &e62) inside
     0x81d14  lw a0,0(a0) (the type); e62.type := a0; a0 := (a2 = 2) ? 4 : 8; a2 := (a2 = 3) ? 0 : a0 (the size);
              e62.size := a2; bltu a2,a1 -> 0x81d4c; else a2 := a1
     0x81d4c  a0 := ~s2; 0x81d50 bgeu a0,a2 -> 0x81f2c (else the trap)   pointer overflow of the source
     0x81f2c  s10 := s2 + a2; s8 := a1 - a2; a0 := [R+0x130] (= &e62.body); a1 := s2
     0x81f3c  jal __asan_memcpy (0x518b8), ra = 0x81f40
   THE PROOF. The engine state at the entry holds the registers as their own atoms and two extra atoms: 32 = F,
   33 = t (the input byte, 0 when none is left). The cells [R+0x130, R+0x138) (&e62.body) and [R+0x150, R+0x158)
   (&e62) are regions based at s1 without a write window. e62's header [F+0x210, F+0x218) is a region based at atom 32
   with that write window (in the side-stack frame (4, pos)); the table t[] (16 bytes of .rodata at 0x211c0) is a
   base-free image region; its two shadow bytes SHADOW_OFF + 0x4238 .. 0x4239 are a zero region based at s4 (their
   value 0 follows from the table's range_addressable), so the table's check at a literal address is decided by the
   engine: the slow block, whose register a4 lies outside the clobber list, is never entered.
     no byte left: s6 pinned to 0; one run (lib/Reusable/YCbq.v aj_run_to) to the trap test 0x81d50, which the
       engine leaves open (~c is outside its interval arithmetic); the branch split (srr_branch_sh), the trap arm
       refuted from c < 2^47, one run to 0x518b8.
     a byte t: the byte a one-byte region based at s2; the atom facts a6 = 1 and 2 <= c <= 2^47 - 2 decide the trap
       test 0x819a8 and the AND range decides 0x819d8; one run of the token engine (YCbq aj_run_to_tok over
       lib/Reusable/YCbn.v) to 0x81d00, which leaves the input's check obligation; then t & 3 = j is split (four
       cases), a2 and a0 pinned to the literals j and 0x211c0 + 4 j, the input region dropped and e62's header, the
       table and its shadow region added (h6_reseat; the table lies in the image, the frame does not:
       AR_client_img_law); one run to the `bltu` 0x81d44, the branch split, one run to the trap test 0x81d50, the
       split with the trap arm refuted, one run to 0x518b8.
   At 0x518b8 the registers are read from the final symbolic state, e62.type and e62.size from the chunks of e62's
   region, and every byte outside e62's header is kept by the runs' frames. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgStepsB RtPgSegB RtPgW6cBaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the engine states ======================================== *)
Definition H6_TB : Z := 0x81d00.   (* the table's check: `srli a3,a0,3` *)
(* the real frame's cells: [R+0x130] = F + 0x218, [R+0x150] = F + 0x210 (atom 32 = F) *)
Definition h6_rC1 : YP09.region := YP09.mkRegion (Some 9%nat) 0x130 0x138 0 0
  [YP09.mkChunk 0x130 (CVal 8 (SOff 32 0x218))].
Definition h6_rC2 : YP09.region := YP09.mkRegion (Some 9%nat) 0x150 0x158 0 0
  [YP09.mkChunk 0x150 (CVal 8 (SOff 32 0x210))].
(* the input byte t at s2 (atom 33) *)
Definition h6_rI : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
(* e62's header, written *)
Definition h6_rE : YP09.region := YP09.mkRegion (Some 32%nat) 0x210 0x218 0x210 0x218 [].
(* case 6's t[] in .rodata *)
Definition h6_rT : YP09.region := YP09.mkRegion None W6CB_T6 (W6CB_T6 + 16) 0 0 [YP09.mkChunk W6CB_T6 (CImg 16)].
(* the table's two shadow bytes, SHADOW_OFF + 0x211c0 / 8 .. + 1, both 0, based at s4 (atom 20) *)
Definition h6_rS : YP09.region := YP09.mkRegion (Some 20%nat) 16952 16954 0 0 [YP09.mkChunk 16952 (CZero 2)].
(* the token engine's facts: a6 = 1, s2 = c, s4 = SHADOW_OFF, s6 = |r| >= 1, t a byte (closed numerals) *)
Definition h6_G1 : facts := mkFacts [(16%nat, mkAF 1 1 0); (18%nat, mkAF 2 140737488355326 0);
  (20%nat, mkAF 2147450880 2147450880 0); (22%nat, mkAF 1 140737488355328 0); (33%nat, mkAF 0 255 0)] [] [].
Definition h6_Bx : sv := SOff 20 0.
Definition h6_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition h6_extra (F t : Z) : list word := [w64 F; w64 t].
Definition h6_ss0 : sstate := mkSS W6CB_D6 sr_atoms [h6_rE; h6_rT; h6_rS; h6_rC1; h6_rC2] None (mkFacts [] [] []).
Definition h6_ss1 : sstate := mkSS W6CB_D6 sr_atoms [h6_rC1; h6_rC2; h6_rI] None h6_G1.
(* at 0x81d00, after the split t & 3 = j *)
Definition h6_ss2 (ss : sstate) (j : Z) : sstate :=
  mkSS (ss_pc ss) (sr_set (sr_set (ss_regs ss) (12%bv : bv 5) (SLit j)) (10%bv : bv 5) (SLit (W6CB_T6 + 4 * j)))
    [h6_rE; h6_rT; h6_rS; h6_rC1; h6_rC2] None (ss_facts ss).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ======================================== arithmetic ======================================== *)
Lemma h6_U_and3 : forall E v, ew E 33 = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_AND (SOff 33 0) (SLit 3)) = v mod 4.
Proof.
intros E v H Hv. rewrite U_and_lit by lia. rewrite (U_atom E 33 v H) by lia.
change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity.
Qed.
(* a0 after `add a0,a0,a3` at 0x819e8, as the engine holds it *)
Lemma h6_U_tbl : forall E v, ew E 33 = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_ADD (SLit 135616) (SAlu ALU_SLL (SAlu ALU_AND (SOff 33 0) (SLit 3)) (SLit 2))) =
  W6CB_T6 + 4 * (v mod 4).
Proof.
intros E v H Hv. pose proof (Z.mod_pos_bound v 4 ltac:(lia)) as Hm.
rewrite U_SAlu, U_SLit, U_SAlu, (h6_U_and3 E v H Hv), U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite (zcanon_id (v mod 4 * 4)) by (unfold M64; lia).
rewrite (zcanon_id 135616) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). unfold W6CB_T6. lia.
Qed.
(* `not a0,s2` as the engine holds it: an xor with the all-ones literal *)
Lemma h6_U_not : forall E n x k z, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 ->
  zcanon z = 2 ^ 64 - 1 -> U E (SAlu ALU_XOR (SOff n k) (SLit z)) = 2 ^ 64 - 1 - (x + k).
Proof.
intros E n x k z Hn Hx Hk Hz. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E n x k Hn Hx Hk), U_SLit, Hz.
rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* a register's symbolic value at a leaf, as a value *)
Lemma h6_den_lit : forall E z v, z = v -> sv_denot E (SLit z) = w64 v.
Proof. intros E z v ->. reflexivity. Qed.
Lemma h6_den_off : forall E n a k v, ew E n = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> 0 <= a + k < 2 ^ 64 -> v = a + k ->
  sv_denot E (SOff n k) = w64 v.
Proof. intros E n a k v H Ha Hak ->. rewrite denot_lit_U, (U_atom_off E n a k H Ha Hak). reflexivity. Qed.
Lemma h6_den_add : forall E n m a b v, ew E n = Z_to_bv 64 a -> ew E m = Z_to_bv 64 b -> 0 <= a -> 0 <= b ->
  a + b < 2 ^ 64 -> v = a + b -> sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = w64 v.
Proof.
intros E n m a b v Hn Hm Ha Hb Hab ->. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n a Hn) by lia. rewrite (U_atom E m b Hm) by lia. rewrite zcanon_id by (unfold M64; lia).
reflexivity.
Qed.
Lemma h6_af : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi H Hv Hb. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. split; [lia | split; [reflexivity | lia]].
Qed.

(* ======================================== the engine state's pieces ======================================== *)
(* the same machine state seen through other registers and regions (the facts kept) *)
Lemma h6_reseat : forall E ss ms rg rs, st_ok rsegs E ss ms -> ss_resv ss = None ->
  regs_ok E rg (ms_regs ms) -> mem_ok rsegs E (ms_mem ms) rs ->
  st_ok rsegs E (mkSS (ss_pc ss) rg rs None (ss_facts ss)) ms.
Proof.
intros E ss ms rg rs (H1 & H2 & H3 & H4 & H5 & H6 & _ & _ & H9) Hrv Hr Hm.
rewrite Hrv in H4. unfold st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact Hr|]. split; [exact Hm | exact H9].
Qed.
(* a run whose regions have no write window keeps every byte *)
Lemma h6_keep0 : forall E rs (H : word -> bool) (m1 m2 : word -> option byte),
  frame_of E rs (mrestrict H m1) (mrestrict H m2) -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros E rs H m1 m2 HF Hro a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.
(* a literal chunk of region i of a run's state, at absolute address a *)
Lemma h6_val_at : forall E ss (H : word -> bool) ms i r off (n : N) z b a,
  st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal n (SLit z))) (YP09.r_chunks r) -> base_val E (YP09.r_base r) = b ->
  0 <= z < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 -> a = b + off ->
  val_mem rsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) z.
Proof.
intros E ss H ms i r off n z b a HS Hi Hc Hb Hz Hn ->.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. specialize (Hok r (nth_error_In _ _ Hi)).
pose proof (YP09.region_ok_chunk rsegs E _ r _ Hok Hc) as Hck. rewrite Hb in Hck.
exact (val_of_chunk_ok rsegs E _ b off n (SLit z) z Hck eq_refl Hz Hn).
Qed.

(* ======================================== the table, its shadow and the frame ======================================== *)
Lemma h6_tbl_img : forall a, W6CB_T6 <= a < W6CB_T6 + 16 -> in_img rsegs a.
Proof.
intros a Ha.
assert (Hx : existsb (fun sg : Segment => (Z.of_N (seg_base sg) <=? W6CB_T6) &&
  (W6CB_T6 + 16 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.
(* e62's header (in a frame for locals, outside the image) and the table (in the image) are apart *)
Lemma h6_e_tbl : forall B ly S W mem md pos, AR_laws rsegs B -> AR rsegs B ly S W mem md -> In (4, pos) (frames S) ->
  frame_addr ly 4 pos + 0x218 <= W6CB_T6 \/ W6CB_T6 + 16 <= frame_addr ly 4 pos + 0x210.
Proof.
intros B ly S W mem md pos LAWS HAR Hin.
destruct (Z_le_gt_dec (frame_addr ly 4 pos + 0x218) W6CB_T6) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (W6CB_T6 + 16) (frame_addr ly 4 pos + 0x210)) as [H'|H']; [right; exact H'|].
exfalso.
pose proof (al_client_img _ _ LAWS ly S W mem md (Z.max (frame_addr ly 4 pos + 0x210) W6CB_T6) HAR) as Hc.
apply (proj2 (Hc ltac:(right; left; exists 4, pos; split; [exact Hin | change (fs_frame_bytes 4) with 1024; lia]))).
apply h6_tbl_img. lia.
Qed.
(* the table's two shadow bytes are 0: each of its granules is whole and addressable *)
Lemma h6_tsh : forall (H : word -> bool) mem, range_addressable (aview rsegs H mem) SHADOW_OFF W6CB_T6 16 ->
  forall i, 0 <= i < 2 -> aview rsegs H mem (SHADOW_OFF + 16952 + i) = Some 0.
Proof.
intros H mem Hra i Hi.
destruct (Hra (W6CB_T6 + 8 * i + 7) ltac:(unfold W6CB_T6; lia)) as (s & Hs & Hok).
assert (Ex : W6CB_T6 + 8 * i + 7 = 7 + (16952 + i) * 8) by (unfold W6CB_T6; lia).
unfold shadow_of_addr in Hs. rewrite Ex, Z.div_add in Hs by lia. change (7 / 8) with 0 in Hs.
rewrite Z.add_0_l, Z.add_assoc in Hs.
destruct Hok as [Hs0 | [Hm Hs8]]; [subst s; exact Hs|].
exfalso. rewrite Ex, Z.mod_add in Hm by lia. change (7 mod 8) with 7 in Hm. lia.
Qed.
Lemma h6_rS_ok : forall E (H : word -> bool) mem, bv_unsigned (ew E 20) = SHADOW_OFF ->
  (forall i, 0 <= i < 2 -> aview rsegs H mem (SHADOW_OFF + 16952 + i) = Some 0) ->
  region_ok rsegs E (mrestrict H mem) h6_rS.
Proof.
intros E H mem U20 Hz. unfold h6_rS.
apply (rtmb_ro_region rsegs E H mem 20%nat SHADOW_OFF); [exact U20 | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia |].
constructor; [|constructor].
apply YI04.chunk_ok_zero. intros i Hi.
specialize (Hz i Hi). unfold aview in Hz.
destruct (mbyte rsegs (mrestrict H mem) (SHADOW_OFF + 16952 + i)) as [bb|] eqn:Hb; cbn [option_map] in Hz;
  [|discriminate Hz].
injection Hz as Hz. f_equal. apply bv_eq. rewrite Hz. reflexivity.
Qed.

Context {SK : YI16.sink_head}.

(* ======================================== tactics ======================================== *)
Ltac h6_kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; h6_kio].
(* the write window of a run's first region (e62's header, based at atom 32 = F = frame_addr lyc 4 pos) *)
Ltac h6_awr U32 HFa Hown pos :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end;
  eapply (rtsb_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 32%nat pos 0);
  [ reflexivity | rewrite U32, Z.add_0_r; exact HFa | exact Hown | cbn; lia | cbn; lia | awr_ok_tac ].
(* after a run: every byte outside e62's header kept since the segment's start *)
Ltac h6_ke F W U32 :=
  lazymatch goal with
  | HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2),
    KE : forall a, 0 <= a < 2 ^ 64 -> ~ _ -> aview _ _ ?m1 a = aview _ _ ?mc a |- _ =>
    let rs' := eval vm_compute in rs in
    let KE' := fresh "KE" in
    assert (KE' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x210 <= a < F + 0x218) ->
      aview rsegs (w_H W) m2 a = aview rsegs (w_H W) mc a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
      intros a Ha Hn; transitivity (aview rsegs (w_H W) m1 a); [|exact (KE a Ha Hn)];
      unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
      rewrite unsigned_lit_small by lia;
      let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Hra := fresh "Hra" in
      intros (rr & Hrr & Hra); change rs with rs' in Hrr; cbn [In] in Hrr;
      repeat (destruct Hrr as [Hrr | Hrr];
        [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra; first [lia | rewrite U32 in Hra; lia] |]);
      destruct Hrr
    | clear KE HFr; rename KE' into KE ]
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* a register of the final state *)
Ltac h6_regv HS :=
  rewrite (st_ok_restrict_reg rsegs _ _ _ _ _ HS);
  match goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
Ltac h6_reg HS :=
  h6_regv HS;
  first [ apply h6_den_lit; first [reflexivity | lia]
        | eapply h6_den_off; [eassumption | lia | lia | lia]
        | eapply h6_den_add; [eassumption | eassumption | lia | lia | lia | lia] ].
(* e62.type / e62.size from the chunk of e62's region (the first region of the final state) *)
Ltac h6_val HS U32 off z :=
  lazymatch type of HS with st_ok _ ?Ex ?ssf (restrict ?H ?msf) =>
    let rr := eval vm_compute in (nth_error (ss_mem ssf) 0) in
    lazymatch rr with Some ?r0 =>
      eapply (h6_val_at Ex ssf H msf 0 r0 off 4%N z);
      [ exact HS | vm_compute; reflexivity | cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right])
      | cbn [YP09.r_base base_val]; exact U32 | cbn; lia | cbn; lia | lia ]
    end
  end.
(* the leaf at 0x518b8: everything but Q *)
Ltac h6_leaf W HAE :=
  apply SRr_ret;
  lazymatch goal with
  | HS : st_ok _ ?Ex ?ssf (restrict _ ?msf), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?memf ?mdf _,
    KE : forall a, 0 <= a < 2 ^ 64 -> ~ _ -> aview _ _ ?memf a = _ |- _ =>
    unfold w6cb_hpost; cbv beta;
    exists (ms_regs msf), (ms_mem msf), mdf;
    split; [reflexivity|];
    split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HS eq_refl) at 1; reflexivity|];
    split; [exact HJ|];
    split; [h6_kio|];
    split; [eapply (RtPgStepsB.regs_kept_of_st_ok rsegs _ _ msf _ _ (w_H W) _ HS HAE); vm_compute; reflexivity|];
    split; [let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
            intros a Ha Hn; exact (KE a Ha Hn)|];
    cbv zeta; cbn [Cursor.fuzz_u8 fst snd]
  end.
(* the nine facts Q states *)
Ltac h6_q HS U32 TY SZ :=
  split; [h6_reg HS|]; split; [h6_reg HS|]; split; [h6_reg HS|]; split; [h6_reg HS|];
  split; [h6_reg HS|]; split; [h6_reg HS|]; split; [h6_reg HS|];
  split; [h6_val HS U32 528 TY | h6_val HS U32 532 SZ].
(* the `bltu a2,a1` 0x81d44 on t1 - 2 = |r1| as a comparison *)
Ltac h6_hc E X6 Hc :=
  rewrite branch_ltu_U, U_SLit, (U_atom_off E 6 _ (-2) X6) in Hc by lia;
  rewrite zcanon_id in Hc by (unfold M64; lia);
  first [apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc].
(* the trap test 0x81d50 `bgeu ~s2, a2`: its trap arm is refuted (c + a2 < 2^64), its other arm goes on;
   s2 is atom 18 (no byte) or s10 + 2 (atom 26, a byte), a2 a literal or t1 - 2 (atom 6) *)
Ltac h6_trap E Xs n k X6 :=
  lazymatch goal with
  | Hc : branch_taken BC_GEU _ _ = false |- _ =>
      exfalso; rewrite branch_geu_U in Hc;
      rewrite (h6_U_not E n _ k _ Xs) in Hc by first [lia | reflexivity];
      first [ rewrite U_SLit, zcanon_id in Hc by (unfold M64; lia)
            | rewrite (U_atom_off E 6 _ (-2) X6) in Hc by lia ];
      apply negb_false_iff in Hc; apply Z.ltb_lt in Hc; lia
  | Hc : branch_taken BC_GEU _ _ = true |- _ => clear Hc
  end.

(* ======================================== the block lemma ======================================== *)
Theorem w6cb_h6 : forall B, w6cb_h6_stmt B.
Proof.
intros B. pose proof (AR_laws_ok rsegs B) as LAWS.
unfold w6cb_h6_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c r
  (HJ & Hgeo & Hrom) Hregs Hcells Hin Hz Hra6.
destruct Hgeo as (HR16 & HRlo & HRhi & HRhm & Hown & HFa & HFapp & HF32).
destruct Hregs as (H2 & H3 & H4 & H9 & H20 & H18 & H22 & H26 & H6 & H16).
destruct Hcells as (V150 & V130 & V0).
destruct Hin as (Hbytes & Hrain & Hhull & Hc1 & Hc63 & Hamr & Hdis).
clear Hz V0.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsl.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
rewrite <- HFa in HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFceil.
unfold T_SEG_STK, ASTACK in HRlo, HRhm, Hdis.
assert (BR : kHighMemBeg + 16384 <= R /\ R + 0x220 <= 2 ^ 47 /\ F + 1024 + 16384 <= R) by lia.
clear Hceil Hslo Hshi H47 HFceil HRlo HRhi HRhm Hstk.
destruct BR as (BR1 & BR2 & BR3). unfold kHighMemBeg in BR1.
assert (HFlo : F + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= F)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp; lia).
clear HFapp.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 0x210 <= a < F + 0x218) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 W6CB_D6) with (Z_to_bv 64 W6CB_D6).
destruct r as [|b r1].
- (* ======== no byte left: t = 0, the type t[0], size 8, n = 0 ======== *)
  cbn [length Z.of_nat] in H22, H6.
  clear Hbytes Hrain Hhull Hdis Hamr.
  destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (_ & _ & Hfp & _).
  rewrite <- HFa in Hfp. change (fs_frame_bytes 4) with 1024 in Hfp.
  pose proof (h6_e_tbl B lyc Sc W memc mdc pos LAWS HAR Hin4) as HET. rewrite <- HFa in HET.
  remember (Ereg regs (h6_extra F 0)) as E0 eqn:HE0.
  assert (E9 : ew E0 9 = Z_to_bv 64 R) by (subst E0; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E18 : ew E0 18 = Z_to_bv 64 c) by (subst E0; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E20 : ew E0 20 = Z_to_bv 64 SHADOW_OFF)
    by (subst E0; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E32 : ew E0 32 = Z_to_bv 64 F) by (subst E0; exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E0 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E0 20) = SHADOW_OFF) by (rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew E0 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (HS : st_ok rsegs E0 h6_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6CB_D6) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. subst E0. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
      + unfold h6_rE. apply (rtmb_rw_region rsegs _ (w_H W) memc 32%nat F); [exact U32 | lia | lia | | constructor].
        intros o Ho. exact (proj1 (Hfp (F + o) ltac:(lia))).
      + unfold h6_rT. apply (img_region_ok_rom _ W memc W6CB_T6 16);
          [exact Hrom | unfold W6CB_T6; lia | unfold W6CB_T6; lia | lia | vm_compute; reflexivity].
      + apply h6_rS_ok; [exact U20 | exact (h6_tsh _ _ Hra6)].
      + unfold h6_rC1. apply (rtmb_ro_region rsegs _ (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
        constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ R 0x130 8 (SOff 32 0x218) (F + 0x218));
          [eapply h6_den_off; [exact E32 | lia | lia | lia] | cbn; lia | cbn; lia | exact V130].
      + unfold h6_rC2. apply (rtmb_ro_region rsegs _ (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
        constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ R 0x150 8 (SOff 32 0x210) (F + 0x210));
          [eapply h6_den_off; [exact E32 | lia | lia | lia] | cbn; lia | cbn; lia | exact V150].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, h6_rE, h6_rT, h6_rS, h6_rC1, h6_rC2.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20, U32.
      unfold W6CB_T6, SHADOW_OFF in *. repeat split; lia.
    - split; [exact I | split; exact I]. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (22%bv : bv 5) 0 HS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; exact H22)) as HS1.
  clear HS. rename HS1 into HS.
  assert (HAE : env_agree 32 (Ereg regs (h6_extra F 0)) E0) by (subst E0; apply env_agree_refl).
  clear HE0 Hfp HET.
  (* 0x819a0 .. the trap test 0x81d50: the table's check (zero shadow), the type, e62.type, the size, e62.size *)
  aj_run_to w6cb_tbl_ok HS HJ W6CB_CPY; [h6_awr U32 HFa Hown pos|].
  h6_ke F W U32.
  srr_branch_sh w6cb_tbl_ok HS.
  all: h6_trap E0 E18 18%nat 0 E18.
  (* .. 0x518b8 *)
  aj_run_to w6cb_tbl_ok HS HJ W6CB_CPY; [h6_awr U32 HFa Hown pos|].
  h6_ke F W U32.
  h6_leaf W HAE.
  cbn [length Z.of_nat].
  change (w6cb_ty6 0) with 5. change (w6cb_sz6 5) with 8.
  h6_q HS U32 5 8.
- (* ======== a byte t, the rest r1 ======== *)
  pose proof (Cursor.byte_range b) as Ht.
  assert (Hlen : Z.of_nat (length (b :: r1)) = Z.of_nat (length r1) + 1) by (cbn [length]; lia).
  pose proof (proj1 (rtmb_bytes_aview rsegs (w_H W) memc c (b :: r1)) Hbytes 0%nat ltac:(cbn [length]; lia)) as Hb0.
  cbn [nth Z.of_nat] in Hb0. rewrite Z.add_0_r in Hb0.
  assert (Hcr : 2 <= c /\ c + Z.of_nat (length (b :: r1)) < 2 ^ 47).
  { unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia. }
  assert (Hdc : (c + 1 <= R + 0x58 \/ R + 0x148 <= c) /\ (c + 1 <= R + 0x150 \/ R + 0x180 <= c)).
  { destruct (Hdis c ltac:(lia)) as (_ & _ & D3 & D4 & _). lia. }
  clear Hdis Hamr Hhull Hc63.
  remember (Ereg regs (h6_extra F (bv_unsigned b))) as E1 eqn:HE1.
  assert (E6 : ew E1 6 = Z_to_bv 64 (Z.of_nat (length (b :: r1)) + 1))
    by (subst E1; rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6).
  assert (E9 : ew E1 9 = Z_to_bv 64 R) by (subst E1; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E16 : ew E1 16 = Z_to_bv 64 1) by (subst E1; rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16).
  assert (E18 : ew E1 18 = Z_to_bv 64 c) by (subst E1; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E20 : ew E1 20 = Z_to_bv 64 SHADOW_OFF)
    by (subst E1; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E22 : ew E1 22 = Z_to_bv 64 (Z.of_nat (length (b :: r1))))
    by (subst E1; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
  assert (E26 : ew E1 26 = Z_to_bv 64 (c - 1)) by (subst E1; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
  assert (E32 : ew E1 32 = Z_to_bv 64 F) by (subst E1; exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E1 33 = Z_to_bv 64 (bv_unsigned b)) by (subst E1; exact (ew_Ereg_extra regs _ 1)).
  assert (U9 : bv_unsigned (ew E1 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U18 : bv_unsigned (ew E1 18) = c) by (rewrite E18; apply unsigned_lit_small; lia).
  assert (HS : st_ok rsegs E1 h6_ss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6CB_D6) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. subst E1. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor; [|constructor]]].
      + unfold h6_rC1. apply (rtmb_ro_region rsegs _ (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
        constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ R 0x130 8 (SOff 32 0x218) (F + 0x218));
          [eapply h6_den_off; [exact E32 | lia | lia | lia] | cbn; lia | cbn; lia | exact V130].
      + unfold h6_rC2. apply (rtmb_ro_region rsegs _ (w_H W) memc 9%nat R); [exact U9 | lia | lia |].
        constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ R 0x150 8 (SOff 32 0x210) (F + 0x210));
          [eapply h6_den_off; [exact E32 | lia | lia | lia] | cbn; lia | cbn; lia | exact V150].
      + unfold h6_rI. apply (rtmb_cell_region rsegs _ (w_H W) memc 18%nat c (bv_unsigned b) (SOff 33 0) U18 Hb0);
          [eapply h6_den_off; [exact E33 | lia | lia | lia] | lia | lia].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, h6_rC1, h6_rC2, h6_rI.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18. repeat split; lia.
    - unfold facts_ok, h6_G1. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I].
      split; [apply (h6_af _ _ _ _ _ E16); lia|].
      split; [apply (h6_af _ _ _ _ _ E18); lia|].
      split; [apply (h6_af _ _ _ _ _ E20); unfold SHADOW_OFF; lia|].
      split; [apply (h6_af _ _ _ _ _ E22); lia|].
      split; [apply (h6_af _ _ _ _ _ E33); lia | exact I]. }
  assert (SHOK : sh_ok rsegs h6_Bx [] E1 (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs (h6_extra F (bv_unsigned b))) E1) by (subst E1; apply env_agree_refl).
  clear HE1 Hdc.
  (* 0x819a0 .. 0x81d00: the trap test 0x819a8, the input's check, the byte's load, the trap test 0x819d8 *)
  aj_run_to_tok w6cb_tbl_ok HS HJ SHOK h6_Bspan H6_TB.
  { apply (obl_of_range rsegs (w_H W) memc _ h6_Bx _ _ c (Z.of_nat (length (b :: r1))) Hrain).
    - apply (U_atom _ 20 SHADOW_OFF E20). unfold SHADOW_OFF. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia. }
  { awr_ok_tac. }
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (h6_keep0 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as KEall end.
  h6_ke F W U9.
  lazymatch type of KEall with forall a, aview _ _ ?m1 a = _ =>
    pose proof (rtmb_rom_kept rsegs W W memc m1 Hrom (fun a _ => KEall a)) as Hrom1 end.
  clear KEall.
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs (h6_extra F (bv_unsigned b))) Ex) by env_agree_chain HAE;
    assert (X6 : ew Ex 6 = Z_to_bv 64 (Z.of_nat (length (b :: r1)) + 1)) by (rewrite ?ew_ewset_other by lia; exact E6);
    assert (X9 : ew Ex 9 = Z_to_bv 64 R) by (rewrite ?ew_ewset_other by lia; exact E9);
    assert (X18 : ew Ex 18 = Z_to_bv 64 c) by (rewrite ?ew_ewset_other by lia; exact E18);
    assert (X20 : ew Ex 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite ?ew_ewset_other by lia; exact E20);
    assert (X26 : ew Ex 26 = Z_to_bv 64 (c - 1)) by (rewrite ?ew_ewset_other by lia; exact E26);
    assert (X32 : ew Ex 32 = Z_to_bv 64 F) by (rewrite ?ew_ewset_other by lia; exact E32);
    assert (X33 : ew Ex 33 = Z_to_bv 64 (bv_unsigned b)) by (rewrite ?ew_ewset_other by lia; exact E33);
    remember Ex as E2 eqn:HE2
  end.
  clear HE2 HAE E6 E9 E16 E18 E20 E22 E26 E32 E33 U9 U18 SHOK.
  assert (V9 : bv_unsigned (ew E2 9) = R) by (rewrite X9; apply unsigned_lit_small; lia).
  assert (V20 : bv_unsigned (ew E2 20) = SHADOW_OFF) by (rewrite X20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (V32 : bv_unsigned (ew E2 32) = F) by (rewrite X32; apply unsigned_lit_small; lia).
  (* at 0x81d00: a2 = t & 3 and a0 = 0x211c0 + 4 (t & 3); the table's shadow bytes as at the entry *)
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    assert (G12 : getr (ms_regs msx) (12%bv : bv 5) = Z_to_bv 64 (bv_unsigned b mod 4))
      by (h6_regv HS; rewrite denot_lit_U, (h6_U_and3 _ _ X33 Ht); reflexivity);
    assert (G10 : getr (ms_regs msx) (10%bv : bv 5) = Z_to_bv 64 (W6CB_T6 + 4 * (bv_unsigned b mod 4)))
      by (h6_regv HS; rewrite denot_lit_U, (h6_U_tbl _ _ X33 Ht); reflexivity);
    assert (HSH : forall i, 0 <= i < 2 -> aview rsegs (w_H W) (ms_mem msx) (SHADOW_OFF + 16952 + i) = Some 0)
      by (intros i Hi; rewrite KE by (unfold SHADOW_OFF; lia); exact (h6_tsh _ _ Hra6 i Hi))
  end.
  pose proof HJ as (HAR1 & _).
  destruct (al_frames _ _ LAWS lyc Sc W _ _ 4 pos HAR1 Hin4) as (_ & _ & Hfp & _).
  rewrite <- HFa in Hfp. change (fs_frame_bytes 4) with 1024 in Hfp.
  pose proof (h6_e_tbl B lyc Sc W memc mdc pos LAWS HAR Hin4) as HET. rewrite <- HFa in HET.
  clear HAR1 HAR.
  pose proof (Z.mod_pos_bound (bv_unsigned b) 4 ltac:(lia)) as Hm4.
  assert (Hj : bv_unsigned b mod 4 = 0 \/ bv_unsigned b mod 4 = 1 \/ bv_unsigned b mod 4 = 2 \/
               bv_unsigned b mod 4 = 3) by lia.
  destruct Hj as [Hj|[Hj|[Hj|Hj]]].
  all: lazymatch type of Hj with _ = ?j =>
    let TY := eval vm_compute in (nth (Z.to_nat j) Tables.t6 0) in
    let SZ := eval vm_compute in (w6cb_sz6 TY) in
    assert (Hty : w6cb_ty6 (bv_unsigned b) = TY) by (unfold w6cb_ty6; rewrite Hj; reflexivity);
    assert (Hsz : w6cb_sz6 TY = SZ) by reflexivity;
    lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
      assert (HS2 : st_ok rsegs E2 (h6_ss2 ssx j) (restrict (w_H W) msx));
      [ unfold h6_ss2; apply h6_reseat; [exact HS | reflexivity | |];
        [ apply regs_ok_pin;
          [ apply regs_ok_pin;
            [ exact (st_ok_regs_ok rsegs _ _ _ HS)
            | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X
            | change (ms_regs (restrict (w_H W) msx)) with (ms_regs msx); rewrite G12, Hj; reflexivity ]
          | intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X
          | change (ms_regs (restrict (w_H W) msx)) with (ms_regs msx); rewrite G10, Hj; reflexivity ]
        | pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HRs & _);
          change (ms_mem (restrict (w_H W) msx)) with (mrestrict (w_H W) (ms_mem msx)) in HRs |- *;
          split; [vm_compute; reflexivity|]; split;
          [ constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]];
            [ unfold h6_rE; apply (rtmb_rw_region rsegs _ (w_H W) (ms_mem msx) 32%nat F);
              [exact V32 | lia | lia | intros o Ho; exact (proj1 (Hfp (F + o) ltac:(lia))) | constructor]
            | unfold h6_rT; apply (img_region_ok_rom _ W (ms_mem msx) W6CB_T6 16);
              [exact Hrom1 | unfold W6CB_T6; lia | unfold W6CB_T6; lia | lia | vm_compute; reflexivity]
            | apply h6_rS_ok; [exact V20 | exact HSH]
            | apply (proj1 (Forall_forall _ _) HRs); vm_compute; left; reflexivity
            | apply (proj1 (Forall_forall _ _) HRs); vm_compute; right; left; reflexivity ]
          | cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint, h6_rE, h6_rT, h6_rS, h6_rC1, h6_rC2;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite V9, V20, V32; unfold W6CB_T6, SHADOW_OFF in *;
            repeat split; lia ] ]
      | clear HS; rename HS2 into HS ]
    end
  end.
  all: clear G10 G12 HSH Hfp HET.
  (* 0x81d00 .. the `bltu a2,a1` 0x81d44: the table's check (zero shadow), the type, e62.type, the size, e62.size *)
  all: (aj_run_to w6cb_tbl_ok HS HJ W6CB_CPY; [h6_awr V32 HFa Hown pos|]).
  all: h6_ke F W V32.
  all: srr_branch_sh w6cb_tbl_ok HS.
  all: h6_hc E2 X6 Hc.
  all: rename Hc into Hlt.
  (* .. the trap test 0x81d50 *)
  all: (aj_run_to w6cb_tbl_ok HS HJ W6CB_CPY; [h6_awr V32 HFa Hown pos|]).
  all: h6_ke F W V32.
  all: srr_branch_sh w6cb_tbl_ok HS.
  all: h6_trap E2 X26 26%nat 2 X6.
  (* .. 0x518b8 *)
  all: (aj_run_to w6cb_tbl_ok HS HJ W6CB_CPY; [h6_awr V32 HFa Hown pos|]).
  all: h6_ke F W V32.
  all: h6_leaf W HAE2.
  all: rewrite Hty, Hsz.
  all: lazymatch type of Hty with _ = ?TY => lazymatch type of Hsz with _ = ?SZ => h6_q HS V32 TY SZ end end.
Qed.
End b.

Print Assumptions w6cb_h6.
