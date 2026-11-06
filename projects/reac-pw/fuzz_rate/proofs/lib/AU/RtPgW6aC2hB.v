(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aC2h.v at 616508a91de2 for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) instead of a lib/A/Img0 module; every pc and the ints table address are rate's; the registers are rate's (s2 the shadow offset, s9 the cursor, s8 what is left, a5 what was left before the kind byte, s6 the reloaded shadow address); the real frame holds one cell [R+0xe8] (no [R+0xf8] cell: a1 := a5 - 2), so the s1 region has one chunk and the input byte is the extra env slot 33; with no byte left s8 is pinned to 0 (not s9); the chaining lemma is RtPgSteps.rts_blk_seq. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aC2h.v at 88912827c774; ported to the same unit's image B (fuzz_rate.asan-ubsan): images.AsanUbsan and lib/AU/RtPgStepsB.v / RtPgW6aBaseB.v; every pc is image B's; the registers are image B's (s4 the shadow offset, s2 the cursor, s6 what is left, s10 the kind byte's address, t1 what was left before it, a6 = 1, a1 the byte and the int's address); the cell is [R+0x150] and is read by the odd arm and by the load block; the head passes a pointer-overflow test of s2 (an atom range) and the index block a table-bound test (split and refuted for all 256 bytes); the index block starts after the parity branch and ends at the load block 0x81b34, which with no byte left is reached directly. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the block lemma w6b_c2h of
   lib/AU/RtPgW6aBaseB.v, the head of case 2 of ent_build's `switch (kind % 10)` (pod.h:298-303) inside
   LLVMFuzzerTestOneInput. Proves no function (kind: segment lemma).

   THE CODE (registers as in RtPgW6aBaseB.v: s1 = R, s4 = SHADOW_OFF, s2 = c the cursor, s6 = |r|, s10 = c - 1,
   t1 = |r| + 1, a6 = 1):
     0x817c4  beqz s6 -> 0x81b28                    no byte left: m = 0
     0x817c8 .. 0x817d0  addi a0,s2,1; bltu a6,a0 (else the `unimp`: never, s2 >= 2)
     0x817d4 .. 0x817e0  the shadow check of s2 (slow block 0x822a4)
     0x817e4  lbu a1,0(s2) (= m); a2 := t1 - 2; a3 := m & 1; s2 := s10 + 2
     0x817f4  bnez a3 -> 0x81e54                    m odd: 0x81e54 s6 := [R+0x150], stop at 0x81e58 (W6B_U2)
     0x817f8 .. 0x81820  a3 := 4 * ((m >> 1) % 14) (`ld` of the constant at 0x10318, mulhu), a1 := 0x210e0
     0x81824  not a4,a1; 0x81828 bgeu a4,a3 -> 0x81830 (else the `unimp`)
     0x81830  a1 := a1 + a3; j 0x81b34
     0x81b28  a2 := 0; a1 := 0x210e0                 (then 0x81b34)
     0x81b34 .. 0x81b48  the shadow check of a1, 4 bytes (slow block 0x82260), with s6 := [R+0x150], a4 := 4 inside
     0x81b4c  lw a1,0(a1); j 0x8203c (W6B_TB2)
   THE PROOF is cut in four blocks, each an entry state, one engine run (lib/Reusable/YCbn.v, the token engine that
   follows each slow block itself and leaves one obligation `range_addressable ...` per check) and its post:
     c2_ld_block   0x81b34 .. 0x8203c: a1 is the register atom x11, the int's 4 bytes a one-chunk region based at
                   it (their value the extra env slot 33), the cell [R+0x150] a region based at s1 (slot 32); a
                   literal or computed a1 would not show the engine the check's `(x >> 3) + s4` form. The bytes come
                   from the image (rom_view, c2_ints_ok).
     c2_idx_block  0x817f8 .. 0x81b34: the 8-byte constant as a base-free image region; the table-bound branch
                   0x81828 split by srr_branch_tok, its `unimp` arm refuted and a1's value checked for all 256 m.
     c2_int_block  the two chained by RtPgStepsB.rtsb_blk_seq.
     w6b_c2h       0x817c4 .. 0x817f8 / 0x81e58 / 0x81b34: the cell [R+0x150] as a region based at s1, the input
                   byte as a one-byte region based at s2 whose value is the extra env slot 33, s2's range [2, 2^47 - 2]
                   and a6's range [1, 1] (the pointer-overflow test), s6's range; the branch on m & 1 split by
                   srr_branch_tok (YCbm.v); the even arm chained with c2_int_block and the no-byte arm with
                   c2_ld_block by c2_chain. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgStepsB RtPgW6aBaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term (as
   RtPgStepsB.v) *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the blocks' states ======================================== *)
Definition C2_IDX : Z := 0x817f8.    (* m even: the int's index *)
Definition C2_LD : Z := 0x81b34.     (* a1 = the int's address: the check and the `lw` *)
Definition C2_K14 : Z := 0x10318.    (* the 8-byte constant ceil(2^64 / 14) *)
(* the shadow base is s4's own atom, pinned to SHADOW_OFF by a fact *)
Definition c2_Bx : sv := SOff 20 0.
Definition c2_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition c2_shf : nat * afact := (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
Definition c2_facts0 : facts := mkFacts [c2_shf] [] [].
(* the real frame's cell the odd arm and the load block read: [R+0x150] = vb (slot 32) *)
Definition c2_s1_region : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x150 0x158 0 0 [YP09.mkChunk 0x150 (CVal 8 (SOff 32 0))].
(* the head with a byte left: m at c (slot 33); s2 in [2, 2^47 - 2], s6 = |r| in [1, 2^47 - 1], a6 = 1, m < 256 *)
Definition c2_in_region : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition c2_facts1 : facts :=
  mkFacts [c2_shf; (18%nat, mkAF 2 140737488355326 0); (22%nat, mkAF 1 140737488355327 0);
           (16%nat, mkAF 1 1 0); (33%nat, mkAF 0 255 0)] [] [].
Definition c2_ss1 : sstate := mkSS W6B_D2 sr_atoms [c2_s1_region; c2_in_region] None c2_facts1.
Definition c2_extra1 (vb m : Z) : list word := [w64 vb; w64 m].
(* the head with no byte left (s6 pinned to 0) *)
Definition c2_ss0 : sstate := mkSS W6B_D2 sr_atoms [] None c2_facts0.
(* the index block *)
Definition c2_k14_region : YP09.region := YP09.mkRegion None C2_K14 (C2_K14 + 8) 0 0 [YP09.mkChunk C2_K14 (CImg 8)].
Definition c2_ssi : sstate := mkSS C2_IDX sr_atoms [c2_k14_region] None c2_facts0.
(* the load block: a1 = W6B_INTS + 4 i, its 4 bytes the value of slot 33; [R+0x150] = vb (slot 32) *)
Definition c2_ld_region : YP09.region := YP09.mkRegion (Some 11%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition c2_factsl : facts := mkFacts [c2_shf; (11%nat, mkAF 135392 135444 2)] [] [].
Definition c2_ssl : sstate := mkSS C2_LD sr_atoms [c2_s1_region; c2_ld_region] None c2_factsl.
Definition c2_extral (vb v : Z) : list word := [w64 vb; w64 v].
(* ints[i] as the 4 bytes hold it *)
Definition c2_int32 (i : Z) : Z := nth (Z.to_nat i) Tables.ints 0 mod 2 ^ 32.

(* ======================================== the arithmetic ======================================== *)
(* every atom holds z *)
Definition c2_envz (z : Z) : env := mkEnv (fun _ => Z_to_bv 64 z) (fun _ => []).
Lemma c2_all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
split; [lia | apply in_seq; lia].
Qed.
(* a branch the engine stopped at, whose operands depend on the byte m only (the atom of Hn): its value for all
   256 bytes *)
Ltac c2_br256 m Hn Hm rhs :=
  lazymatch goal with |- branch_taken ?cc (sv_denot ?E ?a) (sv_denot ?E ?b) = _ =>
    transitivity (branch_taken cc (sv_denot (c2_envz m) a) (sv_denot (c2_envz m) b));
    [ cbn [sv_denot ew c2_envz]; rewrite ?ew_ewset_other by lia; rewrite Hn; reflexivity
    | apply Bool.eqb_prop;
      exact (c2_all256 (fun z => Bool.eqb (branch_taken cc (sv_denot (c2_envz z) a) (sv_denot (c2_envz z) b)) (rhs z))
               ltac:(vm_compute; reflexivity) m Hm) ]
  end.
(* a register's value, whose sv depends on the byte m only: for all 256 bytes *)
Ltac c2_val256 m Hn Hm rhs :=
  lazymatch goal with |- sv_denot ?E ?e = _ =>
    transitivity (sv_denot (c2_envz m) e);
    [ cbn [sv_denot ew c2_envz]; rewrite ?ew_ewset_other by lia; rewrite Hn; reflexivity
    | unfold w64; apply bv_eq; apply Z.eqb_eq;
      exact (c2_all256 (fun z => bv_unsigned (sv_denot (c2_envz z) e) =? bv_unsigned (Z_to_bv 64 (rhs z)))
               ltac:(vm_compute; reflexivity) m Hm) ]
  end.
(* `lw` sign-extends; the low 4 bytes are the value *)
Lemma c2_sext_low : forall v, 0 <= v < 2 ^ 32 -> bv_unsigned (sext 64 (bv_extract 0 32 (Z_to_bv 64 v))) mod 2 ^ 32 = v.
Proof.
intros v Hv. change (2 ^ 32) with (2 ^ Z.of_N 32) at 1.
rewrite <- extract_unsigned_mod. change (bv_extract 0 32 (sext 64 (bv_extract 0 32 (Z_to_bv 64 v))))
  with (low32 (sext 64 (bv_extract 0 32 (Z_to_bv 64 v)))).
rewrite low32_sext32, extract_unsigned_mod, unsigned_lit_small by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). apply Z.mod_small. exact Hv.
Qed.

(* ======================================== the image's bytes ======================================== *)
(* ints[0 .. 14) at 0x210e0: read-only bytes of the image, 4 little-endian bytes each *)
Definition c2_ints_ok : bool :=
  forallb (fun i => forallb (fun k =>
    in_rom_b (W6B_INTS + 4 * Z.of_nat i + Z.of_nat k) && YP08.img_byte_ok rsegs (W6B_INTS + 4 * Z.of_nat i + Z.of_nat k) &&
    match img_byte rsegs (W6B_INTS + 4 * Z.of_nat i + Z.of_nat k) with
    | Some b => bv_unsigned b =? YO0f.le_byte (c2_int32 (Z.of_nat i)) 4 k
    | None => false
    end) (seq 0 4)) (seq 0 14).
Lemma c2_ints_ok_true : c2_ints_ok = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c2_ints_val : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (W : world rsegs) mem i,
  rom_view rsegs W mem -> 0 <= i < 14 ->
  val_mem rsegs (mrestrict (w_H W) mem) (W6B_INTS + 4 * i) 4 (c2_int32 i).
Proof.
intros fx rc W mem i HR Hi k Hk.
pose proof (proj1 (forallb_forall _ _) c2_ints_ok_true (Z.to_nat i) ltac:(apply in_seq; lia)) as H1.
pose proof (proj1 (forallb_forall _ _) H1 k ltac:(apply in_seq; lia)) as H2. cbv beta in H2.
rewrite Z2Nat.id in H2 by lia.
apply andb_prop in H2 as [H2 H4]. apply andb_prop in H2 as [H2 H3].
destruct (mbyte_rom W mem _ HR H2 H3) as (b & Hb & Hm).
rewrite Hm. rewrite Hb in H4. apply Z.eqb_eq in H4. rewrite <- H4. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ======================================== small helpers ======================================== *)
Lemma c2_notin : forall (r : bv 5) (l : list (bv 5)), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros r l H Hin. induction l as [|c l IH]; [exact Hin|]. cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)]. unfold bv_eqb in H1. rewrite Z.eqb_refl in H1. discriminate H1.
Qed.
Lemma c2_nz : forall r : bv 5, (bv_unsigned r =? 0) = false -> bv_unsigned r <> 0.
Proof. intros r H. apply Z.eqb_neq. exact H. Qed.
Lemma c2_ra_eq : forall (rd rd' : reader) Bs a n, (forall x, rd' x = rd x) ->
  range_addressable rd Bs a n -> range_addressable rd' Bs a n.
Proof. intros rd rd' Bs a n He H x Hx. destruct (H x Hx) as (s & Hs & Ho). exists s. rewrite He. auto. Qed.
Lemma c2_af : forall E n v lo hi al, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof. intros E n v lo hi al H Hv Hb Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia. auto. Qed.
(* a run whose regions have no write window keeps every byte *)
Lemma c2_keep_step : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
  (forall a, aview rsegs H m1 a = aview rsegs H m0 a) ->
  frame_of E rs (mrestrict H m1) (mrestrict H m2) -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros E rs H m0 m1 m2 K HF Hro a. rewrite <- (K a). unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.
Ltac c2_keep :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, aview _ _ _ a = _ |- _ =>
    let KS := fresh "KS" in
    pose proof (c2_keep_step _ _ _ _ _ _ KE HFr ltac:(vm_compute; reflexivity)) as KS;
    clear KE HFr; rename KS into KE
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with old : machine_state |- _ => clear old end.
(* a register of the state after a run, as its symbolic value's denotation *)
Ltac c2_regv HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity);
    cbn [sv_denot]; rewrite ?ew_ewset_other by lia
  end.
Ltac c2_kio := first [apply same_io_refl | eapply same_io_trans; [| apply RtPgStepsB.same_io_wvb]; c2_kio].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma c2_rom_eq : forall (W W' : world rsegs) m m', (forall a, aview rsegs (w_H W') m' a = aview rsegs (w_H W) m a) ->
  rom_view rsegs W m -> rom_view rsegs W' m'.
Proof. intros W W' m m' He HR a Ha. rewrite He. exact (HR a Ha). Qed.
Lemma c2_vm_eq : forall (W W' : world rsegs) m m' a n v, (forall x, aview rsegs (w_H W') m' x = aview rsegs (w_H W) m x) ->
  val_mem rsegs (mrestrict (w_H W) m) a n v -> val_mem rsegs (mrestrict (w_H W') m') a n v.
Proof. intros W W' m m' a n v He H. apply (val_mem_kept rsegs (w_H W) (w_H W') m m' a n v); [intros k _; apply He | exact H]. Qed.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the leaf of a run into rtsb_blk_post: everything but R *)
Ltac c2_leaf HAE Rtac :=
  apply SRr_ret;
  lazymatch goal with
  | HS : st_ok _ _ _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
    KE : forall a, aview _ _ _ a = _ |- _ =>
    red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
    split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
    split; [exact HJ|];
    split; [eapply (regs_kept_of_st_ok rsegs _ _ ms _ _ (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity]|];
    split; [reflexivity|];
    split; [apply Permutation_refl|];
    split; [c2_kio|];
    split; [apply mo_le_refl; exact MTL|];
    split; [exact KE | Rtac]
  end.

(* a block that starts where a run stopped, re-stated over the run's own start *)
Lemma c2_chain : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc regs1 mem1 md1 pc1 pc2
  (clob1 clob2 clob : list (bv 5)) (R2 R : bvmap 5 word -> Prop),
  (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
  same_io mdc md1 ->
  (forall a, aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
  incl clob1 clob -> incl clob2 clob ->
  (forall regs2, R2 regs2 -> (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob2 -> getr regs2 r = getr regs1 r) -> R regs2) ->
  SRr rsegs W (cfg_at rsegs pc1 regs1 mem1 md1)
    (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 lyc Sc W mem1 md1 pc2 clob2 R2) ->
  SRr rsegs W (cfg_at rsegs pc1 regs1 mem1 md1)
    (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc2 clob R).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc regs1 mem1 md1 pc1 pc2 clob1 clob2 clob R2 R
  Hr1 Hio1 Hm1 Hi1 Hi2 HRR H.
eapply SRr_mono; [exact H|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; rewrite (Hr2 r Hr0 ltac:(intros X; apply Hn; apply Hi2; exact X));
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply Hi1; exact X]|].
split; [exact Hf2|]. split; [exact Hp2|]. split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
split; [exact Hmo2|]. split; [intros a; rewrite (Hm2 a); apply Hm1|].
exact (HRR regs2 HR2 Hr2).
Qed.

(* ---- 0x81b34 .. 0x8203c: the check of the int, s6 := [R+0x150], a4 := 4, the `lw` ---- *)
Lemma c2_ld_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) i R vb,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> rom_view rsegs W memc ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_INTS 56 ->
  getr regs 11 = w64 (W6B_INTS + 4 * i) -> 0 <= i < 14 -> getr regs 20 = w64 SHADOW_OFF ->
  getr regs 9 = w64 R -> W6B_INTS + 56 <= R -> R + 0x158 <= 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 vb -> 0 <= vb < 2 ^ 64 ->
  SRr rsegs W (cfg_at rsegs C2_LD regs memc mdc)
  (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_TB2 [10; 11; 13; 14; 22]%bv
    (fun regs2 => (exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = nth (Z.to_nat i) Tables.ints 0 mod 2 ^ 32) /\
       getr regs2 14 = w64 4 /\ getr regs2 22 = w64 vb)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i R vb HJ HR Hra H11 Hi H20 H9 HRlo HRhi Hvb Hvbr.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
assert (E9 : ew (Ereg regs (c2_extral vb (c2_int32 i))) 9 = Z_to_bv 64 R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E11 : ew (Ereg regs (c2_extral vb (c2_int32 i))) 11 = Z_to_bv 64 (W6B_INTS + 4 * i))
  by (rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E20 : ew (Ereg regs (c2_extral vb (c2_int32 i))) 20 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E32 : ew (Ereg regs (c2_extral vb (c2_int32 i))) 32 = Z_to_bv 64 vb) by exact (ew_Ereg_extra regs _ 0).
assert (E33 : ew (Ereg regs (c2_extral vb (c2_int32 i))) 33 = Z_to_bv 64 (c2_int32 i)) by exact (ew_Ereg_extra regs _ 1).
assert (Hv : 0 <= c2_int32 i < 2 ^ 32) by (unfold c2_int32; apply Z.mod_pos_bound; lia).
assert (HS : st_ok rsegs (Ereg regs (c2_extral vb (c2_int32 i))) c2_ssl
  (restrict (w_H W) (mkst regs (Z_to_bv 64 C2_LD) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, c2_s1_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by (unfold W6B_INTS in HRlo; lia).
      split; [unfold W6B_INTS in HRlo; lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ _ 0x150 8 (SOff 32 0) vb);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hvb].
    + unfold region_ok, c2_ld_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E11, unsigned_lit_small by (unfold W6B_INTS; lia).
      split; [unfold W6B_INTS; lia|]. split; [unfold W6B_INTS; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 33 0) (c2_int32 i)).
      * cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). exact Hv.
      * cbn. lia.
      * rewrite Z.add_0_r. exact (c2_ints_val W memc i HR Hi).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c2_s1_region, c2_ld_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E11, !unsigned_lit_small by (unfold W6B_INTS in *; lia).
    split; [split; [unfold W6B_INTS in *; lia | exact I] | split; exact I].
  - unfold facts_ok. cbn [c2_factsl c2_shf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|split; [|exact I]].
    + apply (c2_af _ _ _ _ _ _ E20); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
    + apply (c2_af _ _ _ _ _ _ E11); unfold W6B_INTS; [lia | lia | | lia].
      rewrite (Z.mul_comm 4 i). change (2 ^ 2) with 4. rewrite Z.mod_add by lia. reflexivity. }
assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs (c2_extral vb (c2_int32 i))) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (c2_extral vb (c2_int32 i))) (Ereg regs (c2_extral vb (c2_int32 i))))
  by apply env_agree_refl.
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
unfold cfg_at. change (w64 C2_LD) with (Z_to_bv 64 C2_LD).
aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan W6B_TB2.
- apply (obl_of_range rsegs (w_H W) memc _ c2_Bx _ _ W6B_INTS 56 Hra).
  + apply (U_atom _ 20 SHADOW_OFF E20). unfold SHADOW_OFF. lia.
  + rewrite (U_atom _ 11 (W6B_INTS + 4 * i) E11) by (unfold W6B_INTS; lia). lia.
  + rewrite (U_atom _ 11 (W6B_INTS + 4 * i) E11) by (unfold W6B_INTS; lia). lia.
- awr_ok_tac.
- c2_keep.
  c2_leaf HAE idtac.
  split.
  { lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
      exists (bv_unsigned (getr (ms_regs ms) 11)); split; [unfold w64; symmetry; apply Z_to_bv_bv_unsigned|] end.
    c2_regv HS (11%bv : bv 5). rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite c2_sext_low by exact Hv. reflexivity. }
  split.
  { c2_regv HS (14%bv : bv 5). reflexivity. }
  { c2_regv HS (22%bv : bv 5). rewrite E32, unsigned_lit_small by lia. unfold w64. f_equal; lia. }
Qed.

(* ---- 0x817f8 .. 0x81b34: the index (m >> 1) % 14, the table-bound test and the address ---- *)
Lemma c2_idx_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) m,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> rom_view rsegs W memc ->
  getr regs 11 = w64 m -> 0 <= m < 256 -> getr regs 20 = w64 SHADOW_OFF ->
  SRr rsegs W (cfg_at rsegs C2_IDX regs memc mdc)
  (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc C2_LD [11; 13; 14]%bv
    (fun regs2 => getr regs2 11 = w64 (W6B_INTS + 4 * ((m / 2) mod 14)))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m HJ HR H11 Hm H20.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
assert (E11 : ew (Ereg regs []) 11 = Z_to_bv 64 m) by (rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E20 : ew (Ereg regs []) 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (HS : st_ok rsegs (Ereg regs []) c2_ssi (restrict (w_H W) (mkst regs (Z_to_bv 64 C2_IDX) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply img_region_ok_rom; [exact HR | unfold C2_K14; lia | unfold C2_K14; lia | lia | vm_compute; reflexivity].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [c2_facts0 c2_shf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I].
    apply (c2_af _ _ _ _ _ _ E20); unfold SHADOW_OFF; [lia | lia | reflexivity | lia]. }
assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
unfold cfg_at. change (w64 C2_IDX) with (Z_to_bv 64 C2_IDX).
(* 0x817f8 .. the table-bound test at 0x81828, which the engine leaves open *)
aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan C2_LD; [awr_ok_tac|].
c2_keep.
srr_branch_tok w6b_tbl_ok HS SHOK c2_Bspan.
- (* the test holds: on to 0x81830 and 0x81b34 *)
  aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan C2_LD; [awr_ok_tac|].
  c2_keep.
  c2_leaf HAE idtac.
  lazymatch goal with HS : st_ok _ _ ?ssf (restrict _ ?ms) |- _ =>
    rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms 11%bv HS);
    let e := eval vm_compute in (sr_get (ss_regs ssf) (11%bv : bv 5)) in
    replace (sr_get (ss_regs ssf) (11%bv : bv 5)) with e by (vm_compute; reflexivity) end.
  c2_val256 m E11 Hm (fun z => W6B_INTS + 4 * ((z / 2) mod 14)).
- (* the `unimp` arm: the test holds for every byte *)
  exfalso.
  lazymatch type of Hc with branch_taken ?cc (sv_denot ?E ?a) (sv_denot ?E ?b) = false =>
    assert (HT : branch_taken cc (sv_denot E a) (sv_denot E b) = true)
      by (c2_br256 m E11 Hm (fun _ : Z => true)) end.
  rewrite HT in Hc. discriminate Hc.
Qed.

(* ---- 0x817f8 .. 0x8203c: ints[(m >> 1) % 14] ---- *)
Lemma c2_int_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) m R vb,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> rom_view rsegs W memc ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_INTS 56 ->
  getr regs 11 = w64 m -> 0 <= m < 256 -> getr regs 20 = w64 SHADOW_OFF ->
  getr regs 9 = w64 R -> W6B_INTS + 56 <= R -> R + 0x158 <= 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 vb -> 0 <= vb < 2 ^ 64 ->
  SRr rsegs W (cfg_at rsegs C2_IDX regs memc mdc)
  (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_TB2 [10; 11; 13; 14; 22]%bv
    (fun regs2 => (exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = w6b_int_even m mod 2 ^ 32) /\
       getr regs2 14 = w64 4 /\ getr regs2 22 = w64 vb)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m R vb HJ HR Hra H11 Hm H20 H9 HRlo HRhi Hvb Hvbr.
eapply SRr_mono.
- eapply (rtsb_blk_seq B MT MTL).
  + exact (c2_idx_block STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m HJ HR H11 Hm H20).
  + intros W1 ly1 S1 regs1 mem1 md1 Hw HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 HR1.
    apply (c2_ld_block STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 ((m / 2) mod 14) R vb HJ1).
    * exact (c2_rom_eq W W1 memc mem1 Hm1 HR).
    * exact (c2_ra_eq _ _ _ _ _ Hm1 Hra).
    * exact HR1.
    * apply Z.mod_pos_bound. lia.
    * rewrite Hr1; [exact H20 | apply c2_nz; reflexivity | apply c2_notin; reflexivity].
    * rewrite Hr1; [exact H9 | apply c2_nz; reflexivity | apply c2_notin; reflexivity].
    * exact HRlo.
    * exact HRhi.
    * exact (c2_vm_eq W W1 memc mem1 _ _ _ Hm1 Hvb).
    * exact Hvbr.
- intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
  exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ2|].
  split; [intros r Hr0 Hn; apply Hr2; [exact Hr0 | intros X; apply in_app_or in X; destruct X as [X|X];
    [apply Hn; cbn [In] in X |- *; tauto | exact (Hn X)]]|].
  split; [exact Hf2|]. split; [exact Hp2|]. split; [exact Hio2|]. split; [exact Hmo2|]. split; [exact Hm2|].
  exact HR2.
Qed.

(* ======================================== the block lemma ======================================== *)
Lemma w6b_c2h : w6b_c2h_stmt B MT.
Proof using MTL LAWS.
unfold w6b_c2h_stmt, w6b_case_head_stmt. cbv beta iota.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c r Hctx Hin Hra.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & HR).
destruct Hin as (H9 & H20 & H18 & H22 & H26 & H6 & H16 & Hvb & Hvbr & Hc1 & Hg & Hrain & Hc0 & Hcr & Ham & Hdis).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_val as (Hac & _).
unfold T_SEG_STK, ASTACK in HspR, Hdis.
assert (HRb : 0 <= R /\ W6B_INTS + 56 <= R /\ R + 0x220 <= 2 ^ 47) by (unfold W6B_INTS; lia).
clear Hsp0al Hceil Hslo Hshi H47 Hac.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
set (vb := F + 0x210) in *.
destruct r as [|b r'].
- (* no byte left: m = 0 *)
  cbn [Cursor.fuzz_u8 fst snd Z.odd length Nat.sub].
  assert (E20 : ew (Ereg regs []) 20 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (HS : st_ok rsegs (Ereg regs []) c2_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D2) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - unfold facts_ok. cbn [c2_facts0 c2_shf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I]. split; [|exact I].
      apply (c2_af _ _ _ _ _ _ E20); unfold SHADOW_OFF; [lia | lia | reflexivity | lia]. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (22%bv : bv 5) 0 HS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H22; reflexivity)) as HS1.
  clear HS. rename HS1 into HS.
  assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
  unfold cfg_at. change (w64 W6B_D2) with (Z_to_bv 64 W6B_D2).
  aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan C2_LD; [awr_ok_tac|].
  c2_keep.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 C2_LD) mm (seg_rom rsegs)) md) with (cfg_at rsegs C2_LD rg mm md) end.
  eapply (c2_chain STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ _ _ C2_LD W6B_TB2
    [10; 11; 12; 22]%bv [10; 11; 13; 14; 22]%bv _
    (fun regs2 => (exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = nth (Z.to_nat 0) Tables.ints 0 mod 2 ^ 32) /\
       getr regs2 14 = w64 4 /\ getr regs2 22 = w64 vb)).
  + eapply (regs_kept_of_st_ok rsegs _ _ _ regs [] (w_H W) _ HS);
      [env_agree_chain HAE | vm_compute; reflexivity].
  + c2_kio.
  + exact KE.
  + intros x Hx. try unfold w6b_head_clob. cbn [In] in Hx |- *. tauto.
  + intros x Hx. try unfold w6b_head_clob. cbn [In] in Hx |- *. tauto.
  + intros regs2 ((v & Hv & Hvm) & H14 & H22') Hk2.
    split; [exists v; split; [exact Hv | exact Hvm]|].
    split; [exact H14|].
    rewrite (Hk2 (12%bv : bv 5)) by first [apply c2_nz; reflexivity | apply c2_notin; reflexivity].
    rewrite (Hk2 (18%bv : bv 5)) by first [apply c2_nz; reflexivity | apply c2_notin; reflexivity].
    split; [c2_regv HS (12%bv : bv 5); reflexivity|].
    split; [c2_regv HS (18%bv : bv 5); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18; unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia|].
    exact H22'.
  + apply (c2_ld_block STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k _ 0 R vb HJ).
    * exact (c2_rom_eq W W memc _ KE HR).
    * exact (c2_ra_eq _ _ _ _ _ KE Hra).
    * c2_regv HS (11%bv : bv 5). unfold w64; f_equal; try (unfold W6B_INTS; lia).
    * lia.
    * c2_regv HS (20%bv : bv 5). rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * c2_regv HS (9%bv : bv 5). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9, Z.add_0_r.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    * lia.
    * lia.
    * exact (c2_vm_eq W W memc _ _ _ _ KE Hvb).
    * exact Hvbr.
- (* a byte m = b, the rest r' *)
  cbn [Cursor.fuzz_u8 fst snd].
  pose proof (Cursor.byte_range b) as Hmb.
  set (m := bv_unsigned b) in *.
  set (n := Z.of_nat (length (b :: r'))) in *.
  assert (Hn : n = Z.of_nat (length r') + 1) by (subst n; cbn [length]; lia).
  assert (Hnb : 1 <= n /\ c + n <= 2 ^ 47 - 1).
  { split; [lia|]. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
  assert (Hcd : c < R + 0x150 \/ R + 0x180 <= c).
  { destruct (Hdis c ltac:(lia)) as (_ & Hd). lia. }
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) (c + 0) 1 m).
  { destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]. exact Hv. }
  assert (E6 : ew (Ereg regs (c2_extra1 vb m)) 6 = Z_to_bv 64 (n + 1))
    by (rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6).
  assert (E9 : ew (Ereg regs (c2_extra1 vb m)) 9 = Z_to_bv 64 R)
    by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E16 : ew (Ereg regs (c2_extra1 vb m)) 16 = Z_to_bv 64 1)
    by (rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16).
  assert (E18 : ew (Ereg regs (c2_extra1 vb m)) 18 = Z_to_bv 64 c)
    by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E20 : ew (Ereg regs (c2_extra1 vb m)) 20 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E22 : ew (Ereg regs (c2_extra1 vb m)) 22 = Z_to_bv 64 n)
    by (rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
  assert (E26 : ew (Ereg regs (c2_extra1 vb m)) 26 = Z_to_bv 64 (c - 1))
    by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
  assert (E32 : ew (Ereg regs (c2_extra1 vb m)) 32 = Z_to_bv 64 vb) by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs (c2_extra1 vb m)) 33 = Z_to_bv 64 m) by exact (ew_Ereg_extra regs _ 1).
  assert (HS : st_ok rsegs (Ereg regs (c2_extra1 vb m)) c2_ss1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D2) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor]].
      + unfold region_ok, c2_s1_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ _ 0x150 8 (SOff 32 0) vb);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hvb].
      + unfold region_ok, c2_in_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E18, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ _ 0 1 (SOff 33 0) m);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | exact Hm0].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c2_s1_region, c2_in_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E18, !unsigned_lit_small by lia.
      split; [split; [lia | exact I] | split; exact I].
    - unfold facts_ok. cbn [c2_facts1 c2_shf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
      + apply (c2_af _ _ _ _ _ _ E20); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
      + apply (c2_af _ _ _ _ _ _ E18); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c2_af _ _ _ _ _ _ E22); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c2_af _ _ _ _ _ _ E16); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c2_af _ _ _ _ _ _ E33); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs (c2_extra1 vb m)) (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs (c2_extra1 vb m)) (Ereg regs (c2_extra1 vb m)))
    by apply env_agree_refl.
  unfold cfg_at. change (w64 W6B_D2) with (Z_to_bv 64 W6B_D2).
  (* 0x817c4 .. the branch on m & 1 at 0x817f4 *)
  aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan C2_IDX.
  { apply (obl_of_range rsegs (w_H W) memc _ c2_Bx _ _ c n Hrain).
    - apply (U_atom _ 20 SHADOW_OFF E20). unfold SHADOW_OFF. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia. }
  { awr_ok_tac. }
  c2_keep.
  srr_branch_tok w6b_tbl_ok HS SHOK c2_Bspan.
  + (* m odd: to 0x81e54 and 0x81e58 *)
    lazymatch type of Hc with branch_taken ?cc (sv_denot ?E ?a) (sv_denot ?E ?b) = _ =>
      assert (HP : branch_taken cc (sv_denot E a) (sv_denot E b) = Z.odd m)
        by (c2_br256 m E33 Hmb (fun z => Z.odd z)) end.
    rewrite HP in Hc. rewrite Hc. cbv beta iota.
    aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan W6B_U2; [awr_ok_tac|].
    c2_keep.
    c2_leaf HAE idtac.
    split; [c2_regv HS (12%bv : bv 5); rewrite E6, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    split; [c2_regv HS (18%bv : bv 5); rewrite E26, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    c2_regv HS (22%bv : bv 5). rewrite E32, unsigned_lit_small by lia. unfold w64. f_equal; lia.
  + (* m even: to 0x817f8, then the int *)
    lazymatch type of Hc with branch_taken ?cc (sv_denot ?E ?a) (sv_denot ?E ?b) = _ =>
      assert (HP : branch_taken cc (sv_denot E a) (sv_denot E b) = Z.odd m)
        by (c2_br256 m E33 Hmb (fun z => Z.odd z)) end.
    rewrite HP in Hc. rewrite Hc. cbv beta iota.
    aj_run_to_tok w6b_tbl_ok HS HJ SHOK c2_Bspan C2_IDX; [awr_ok_tac|].
    c2_keep.
    lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
      rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) end.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 C2_IDX) mm (seg_rom rsegs)) md) with (cfg_at rsegs C2_IDX rg mm md) end.
    eapply (c2_chain STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ _ _ C2_IDX W6B_TB2
      [10; 11; 12; 13; 18]%bv [10; 11; 13; 14; 22]%bv _
      (fun regs2 => (exists v, getr regs2 11 = w64 v /\ v mod 2 ^ 32 = w6b_int_even m mod 2 ^ 32) /\
         getr regs2 14 = w64 4 /\ getr regs2 22 = w64 vb)).
    * eapply (regs_kept_of_st_ok rsegs _ _ _ regs (c2_extra1 vb m) (w_H W) _ HS);
        [env_agree_chain HAE | vm_compute; reflexivity].
    * c2_kio.
    * exact KE.
    * intros x Hx. try unfold w6b_head_clob. cbn [In] in Hx |- *. tauto.
    * intros x Hx. try unfold w6b_head_clob. cbn [In] in Hx |- *. tauto.
    * intros regs2 ((v & Hv & Hvm) & H14 & H22') Hk2.
      split; [exists v; split; [exact Hv | exact Hvm]|].
      split; [exact H14|].
      rewrite (Hk2 (12%bv : bv 5)) by first [apply c2_nz; reflexivity | apply c2_notin; reflexivity].
      rewrite (Hk2 (18%bv : bv 5)) by first [apply c2_nz; reflexivity | apply c2_notin; reflexivity].
      split; [c2_regv HS (12%bv : bv 5); rewrite E6, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
      split; [c2_regv HS (18%bv : bv 5); rewrite E26, unsigned_lit_small by lia; unfold w64; f_equal; cbn [length]; lia|].
      exact H22'.
    * apply (c2_int_block STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k _ m R vb HJ).
      -- exact (c2_rom_eq W W memc _ KE HR).
      -- exact (c2_ra_eq _ _ _ _ _ KE Hra).
      -- c2_regv HS (11%bv : bv 5). rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- exact Hmb.
      -- c2_regv HS (20%bv : bv 5). rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- c2_regv HS (9%bv : bv 5). rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- lia.
      -- lia.
      -- exact (c2_vm_eq W W memc _ _ _ _ KE Hvb).
      -- exact Hvbr.
Qed.

End d.
End b.

Print Assumptions w6b_c2h.
