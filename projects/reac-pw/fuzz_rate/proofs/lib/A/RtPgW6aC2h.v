(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aC2h.v at 616508a91de2 for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) instead of a lib/A/Img0 module; every pc and the ints table address are rate's; the registers are rate's (s2 the shadow offset, s9 the cursor, s8 what is left, a5 what was left before the kind byte, s6 the reloaded shadow address); the real frame holds one cell [R+0xe8] (no [R+0xf8] cell: a1 := a5 - 2), so the s1 region has one chunk and the input byte is the extra env slot 33; with no byte left s8 is pinned to 0 (not s9); the chaining lemma is RtPgSteps.rts_blk_seq. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the block lemma w6_c2h of
   lib/A/RtPgW6aBase.v, the head of case 2 of ent_build's `switch (kind % 10)` (pod.h:298-303) inside
   LLVMFuzzerTestOneInput. Proves no function (kind: segment lemma).

   THE CODE (registers as in RtPgW6aBase.v: s1 = R, s2 = SHADOW_OFF, s9 = c the cursor, s8 = |r|, a4 = c - 1,
   a5 = |r| + 1):
     0x816ac  beqz s8 -> 0x819b8                    no byte left: m = 0
     0x816b0 .. 0x816c0  the shadow check of s9 (NE-SLOW, slow block 0x8217c), with `ld s6,0xe8(s1)` inside
     0x816c4  lbu a2,0(s9) (= m); a1 := a5 - 2; a3 := m & 1; s9 := a4 + 2
     0x816d4  beqz a3 -> 0x819c4                    m odd falls through to 0x816d8 (W6_U2)
     0x819b8  a1 := 0; a2 := 0; ld s6,0xe8(s1)      (then 0x819c4)
     0x819c4 .. 0x819f0  a0 := 0x210e0 + 4 * ((m >> 1) % 14) (`ld` of the constant at 0x10318, mulhu, shifts)
     0x819f4 .. 0x81a00  the shadow check of a0 (NE-SLOW, slow block 0x82138)
     0x81a04  lw a2,0(a0); j 0x81d94 (W6_T2)
   THE PROOF is cut in four blocks, each an entry state, one engine run (lib/Reusable/YCbn.v, the token engine that
   follows each NE-SLOW slow block itself and leaves one obligation `range_addressable ...` per check) and its post:
     c2_ld_block   0x819f4 .. 0x81d94: a0 is the register atom x10, the int's 4 bytes a one-chunk region based at
                   it (their value the extra env slot 32); a literal or computed a0 would not show the engine the
                   check's `(x >> 3) + s2` form. The bytes come from the image (rom_view, c2_ints_ok).
     c2_idx_block  0x819c4 .. 0x819f4: the 8-byte constant as a base-free image region; a0's value is checked for
                   all 256 values of m (c2_a0_val).
     c2_int_block  the two chained by RtPgSteps.rts_blk_seq.
     w6_c2h        0x816ac .. 0x819c4 / 0x816d8: the 8-byte cell [R+0xe8] as a region based at s1, the input byte
                   as a one-byte region based at s9 whose value is the extra env slot 33; the branch on m & 1 split
                   by srr_branch_tok (YCbm.v); the even arm and the no-byte arm chained with c2_int_block by
                   c2_chain. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSteps RtPgW6aBase.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term (as
   RtPgSteps.v) *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the blocks' states ======================================== *)
Definition C2_IDX : Z := 0x819c4.    (* m even (or no byte): the int's index *)
Definition C2_PIN : Z := 0x819f4.    (* a0 = the int's address: the check and the `lw` *)
Definition C2_K14 : Z := 0x10318.    (* the 8-byte constant ceil(2^64 / 14) *)
(* the shadow base is s2's own atom, pinned to SHADOW_OFF by a fact *)
Definition c2_Bx : sv := SOff 18 0.
Definition c2_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition c2_shf : nat * afact := (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
Definition c2_facts0 : facts := mkFacts [c2_shf] [] [].
(* the real frame's cell the head reads: [R+0xe8] = vb (slot 32) *)
Definition c2_s1_region : YP09.region := YP09.mkRegion (Some 9%nat) 0xe8 0xf0 0 0 [YP09.mkChunk 0xe8 (CVal 8 (SOff 32 0))].
(* the head with a byte left: m at c (slot 33) *)
Definition c2_in_region : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition c2_facts1 : facts :=
  mkFacts [c2_shf; (25%nat, mkAF 2 (2 ^ 47 - 2) 0); (24%nat, mkAF 1 (2 ^ 47) 0); (33%nat, mkAF 0 255 0)] [] [].
Definition c2_ss1 : sstate := mkSS W6_D2 sr_atoms [c2_s1_region; c2_in_region] None c2_facts1.
Definition c2_extra1 (vb m : Z) : list word := [w64 vb; w64 m].
(* the head with no byte left *)
Definition c2_ss0 : sstate := mkSS W6_D2 sr_atoms [c2_s1_region] None c2_facts0.
Definition c2_extra0 (vb : Z) : list word := [w64 vb].
(* the index block *)
Definition c2_k14_region : YP09.region := YP09.mkRegion None C2_K14 (C2_K14 + 8) 0 0 [YP09.mkChunk C2_K14 (CImg 8)].
Definition c2_ssi : sstate := mkSS C2_IDX sr_atoms [c2_k14_region] None c2_facts0.
(* the load block: a0 = W6_INTS + 4 i, its 4 bytes the value of slot 32 *)
Definition c2_ld_region : YP09.region := YP09.mkRegion (Some 10%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition c2_factsl : facts := mkFacts [c2_shf; (10%nat, mkAF W6_INTS (W6_INTS + 52) 2)] [] [].
Definition c2_ssl : sstate := mkSS C2_PIN sr_atoms [c2_ld_region] None c2_factsl.
(* ints[i] as the 4 bytes hold it *)
Definition c2_int32 (i : Z) : Z := nth (Z.to_nat i) Tables.ints 0 mod 2 ^ 32.

(* ======================================== the arithmetic ======================================== *)
(* a0 at 0x819f4 as the engine computes it from a2 = m (atom 12) *)
Definition c2_hm : sv := SAlu ALU_SRL (SOff 12 0) (SLit 1).
Definition c2_a0 : sv :=
  SAlu ALU_ADD (SLit 0x210e0)
    (SAlu ALU_SLL
       (SAlu ALU_ADD c2_hm
          (SAlu ALU_SUB (SAlu ALU_SLL (SMd M_MULHU c2_hm (SLit 0x124924924924924a)) (SLit 1))
             (SAlu ALU_SLL (SMd M_MULHU c2_hm (SLit 0x124924924924924a)) (SLit 4))))
       (SLit 2)).
(* every atom holds z *)
Definition c2_envz (z : Z) : env := mkEnv (fun _ => Z_to_bv 64 z) (fun _ => []).
Lemma c2_all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
split; [lia | apply in_seq; lia].
Qed.
Lemma c2_a0_val : forall E m, ew E 12 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E c2_a0 = Z_to_bv 64 (W6_INTS + 4 * ((m / 2) mod 14)).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (c2_envz m) c2_a0); [unfold c2_a0, c2_hm; cbn [sv_denot ew c2_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (c2_all256 (fun m => bv_unsigned (sv_denot (c2_envz m) c2_a0) =? bv_unsigned (Z_to_bv 64 (W6_INTS + 4 * ((m / 2) mod 14))))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.
(* `beqz a3` with a3 = m & 1 is taken exactly when m is even *)
Lemma c2_parity : forall E m, ew E 33 = Z_to_bv 64 m -> 0 <= m < 256 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SOff 33 0) (SLit 1))) (sv_denot E (SLit 0)) = negb (Z.odd m).
Proof.
intros E m Hm Hr.
transitivity (branch_taken BC_EQ (sv_denot (c2_envz m) (SAlu ALU_AND (SOff 33 0) (SLit 1))) (sv_denot (c2_envz m) (SLit 0)));
  [cbn [sv_denot ew c2_envz]; rewrite Hm; reflexivity|].
apply Bool.eqb_prop.
exact (c2_all256 (fun m => Bool.eqb (branch_taken BC_EQ (sv_denot (c2_envz m) (SAlu ALU_AND (SOff 33 0) (SLit 1)))
  (sv_denot (c2_envz m) (SLit 0))) (negb (Z.odd m))) ltac:(vm_compute; reflexivity) m Hr).
Qed.
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
    in_rom_b (W6_INTS + 4 * Z.of_nat i + Z.of_nat k) && YP08.img_byte_ok rsegs (W6_INTS + 4 * Z.of_nat i + Z.of_nat k) &&
    match img_byte rsegs (W6_INTS + 4 * Z.of_nat i + Z.of_nat k) with
    | Some b => bv_unsigned b =? YO0f.le_byte (c2_int32 (Z.of_nat i)) 4 k
    | None => false
    end) (seq 0 4)) (seq 0 14).
Lemma c2_ints_ok_true : c2_ints_ok = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c2_ints_val : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (W : world rsegs) mem i,
  rom_view rsegs W mem -> 0 <= i < 14 ->
  val_mem rsegs (mrestrict (w_H W) mem) (W6_INTS + 4 * i) 4 (c2_int32 i).
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
Ltac c2_kio := first [apply same_io_refl | eapply same_io_trans; [| apply RtPgSteps.same_io_wvb]; c2_kio].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma c2_rom_eq : forall (W W' : world rsegs) m m', (forall a, aview rsegs (w_H W') m' a = aview rsegs (w_H W) m a) ->
  rom_view rsegs W m -> rom_view rsegs W' m'.
Proof. intros W W' m m' He HR a Ha. rewrite He. exact (HR a Ha). Qed.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the leaf of a run into rts_blk_post: everything but R *)
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
    (rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 lyc Sc W mem1 md1 pc2 clob2 R2) ->
  SRr rsegs W (cfg_at rsegs pc1 regs1 mem1 md1)
    (rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc2 clob R).
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

(* ---- 0x819f4 .. 0x81d94: the check of the int and its `lw` ---- *)
Lemma c2_ld_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) i,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> rom_view rsegs W memc ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6_INTS 56 ->
  getr regs 10 = w64 (W6_INTS + 4 * i) -> 0 <= i < 14 -> getr regs 18 = w64 SHADOW_OFF ->
  SRr rsegs W (cfg_at rsegs C2_PIN regs memc mdc)
  (rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_T2 [10; 12; 13]%bv
    (fun regs2 => exists v, getr regs2 12 = w64 v /\ v mod 2 ^ 32 = nth (Z.to_nat i) Tables.ints 0 mod 2 ^ 32)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i HJ HR Hra H10 Hi H18.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
assert (E10 : ew (Ereg regs [w64 (c2_int32 i)]) 10 = Z_to_bv 64 (W6_INTS + 4 * i))
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E18 : ew (Ereg regs [w64 (c2_int32 i)]) 18 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E32 : ew (Ereg regs [w64 (c2_int32 i)]) 32 = Z_to_bv 64 (c2_int32 i)) by exact (ew_Ereg_extra regs _ 0).
assert (Hv : 0 <= c2_int32 i < 2 ^ 32) by (unfold c2_int32; apply Z.mod_pos_bound; lia).
assert (HS : st_ok rsegs (Ereg regs [w64 (c2_int32 i)]) c2_ssl
  (restrict (w_H W) (mkst regs (Z_to_bv 64 C2_PIN) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, c2_ld_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10, unsigned_lit_small by (unfold W6_INTS; lia).
    split; [unfold W6_INTS; lia|]. split; [unfold W6_INTS; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 32 0) (c2_int32 i)).
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). exact Hv.
    + cbn. lia.
    + rewrite Z.add_0_r. exact (c2_ints_val W memc i HR Hi).
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [c2_factsl c2_shf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|split; [|exact I]].
    + apply (c2_af _ _ _ _ _ _ E18); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
    + apply (c2_af _ _ _ _ _ _ E10); unfold W6_INTS; [lia | lia | | lia].
      rewrite (Z.mul_comm 4 i). change (2 ^ 2) with 4. rewrite Z.mod_add by lia. reflexivity. }
assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs [w64 (c2_int32 i)]) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs [w64 (c2_int32 i)]) (Ereg regs [w64 (c2_int32 i)])) by apply env_agree_refl.
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
unfold cfg_at. change (w64 C2_PIN) with (Z_to_bv 64 C2_PIN).
aj_run_to_tok w6_tbl_ok HS HJ SHOK c2_Bspan W6_T2.
- apply (obl_of_range rsegs (w_H W) memc _ c2_Bx _ _ W6_INTS 56 Hra).
  + apply (U_atom _ 18 SHADOW_OFF E18). unfold SHADOW_OFF. lia.
  + rewrite (U_atom _ 10 (W6_INTS + 4 * i) E10) by (unfold W6_INTS; lia). lia.
  + rewrite (U_atom _ 10 (W6_INTS + 4 * i) E10) by (unfold W6_INTS; lia). lia.
- awr_ok_tac.
- c2_keep.
  c2_leaf HAE idtac.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
    exists (bv_unsigned (getr (ms_regs ms) 12)); split; [unfold w64; symmetry; apply Z_to_bv_bv_unsigned|] end.
  c2_regv HS (12%bv : bv 5). rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite c2_sext_low by exact Hv. reflexivity.
Qed.

(* ---- 0x819c4 .. 0x819f4: the index (m >> 1) % 14 and the address ---- *)
Lemma c2_idx_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) m,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> rom_view rsegs W memc ->
  getr regs 12 = w64 m -> 0 <= m < 256 -> getr regs 18 = w64 SHADOW_OFF ->
  SRr rsegs W (cfg_at rsegs C2_IDX regs memc mdc)
  (rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc C2_PIN [10; 12; 13]%bv
    (fun regs2 => getr regs2 10 = w64 (W6_INTS + 4 * ((m / 2) mod 14)))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m HJ HR H12 Hm H18.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
assert (E12 : ew (Ereg regs []) 12 = Z_to_bv 64 m) by (rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E18 : ew (Ereg regs []) 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (HS : st_ok rsegs (Ereg regs []) c2_ssi (restrict (w_H W) (mkst regs (Z_to_bv 64 C2_IDX) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply img_region_ok_rom; [exact HR | unfold C2_K14; lia | unfold C2_K14; lia | lia | vm_compute; reflexivity].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [c2_facts0 c2_shf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I].
    apply (c2_af _ _ _ _ _ _ E18); unfold SHADOW_OFF; [lia | lia | reflexivity | lia]. }
assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
unfold cfg_at. change (w64 C2_IDX) with (Z_to_bv 64 C2_IDX).
aj_run_to_tok w6_tbl_ok HS HJ SHOK c2_Bspan C2_PIN; [awr_ok_tac|].
c2_keep.
c2_leaf HAE idtac.
lazymatch goal with HS : st_ok _ _ ?ssf (restrict _ ?ms) |- _ =>
  rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms 10%bv HS);
  replace (sr_get (ss_regs ssf) (10%bv : bv 5)) with c2_a0 by (vm_compute; reflexivity) end.
exact (c2_a0_val _ m E12 Hm).
Qed.

(* ---- 0x819c4 .. 0x81d94: ints[(m >> 1) % 14] ---- *)
Lemma c2_int_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) m,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> rom_view rsegs W memc ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6_INTS 56 ->
  getr regs 12 = w64 m -> 0 <= m < 256 -> getr regs 18 = w64 SHADOW_OFF ->
  SRr rsegs W (cfg_at rsegs C2_IDX regs memc mdc)
  (rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_T2 [10; 12; 13]%bv
    (fun regs2 => exists v, getr regs2 12 = w64 v /\ v mod 2 ^ 32 = w6_int_even m mod 2 ^ 32)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m HJ HR Hra H12 Hm H18.
eapply SRr_mono.
- eapply (rts_blk_seq B MT MTL).
  + exact (c2_idx_block STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m HJ HR H12 Hm H18).
  + intros W1 ly1 S1 regs1 mem1 md1 Hw HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 HR1.
    apply (c2_ld_block STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 ((m / 2) mod 14) HJ1).
    * exact (c2_rom_eq W W1 memc mem1 Hm1 HR).
    * exact (c2_ra_eq _ _ _ _ _ Hm1 Hra).
    * exact HR1.
    * apply Z.mod_pos_bound. lia.
    * rewrite Hr1; [exact H18 | apply c2_nz; reflexivity | apply c2_notin; reflexivity].
- intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
  exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ2|].
  split; [intros r Hr0 Hn; apply Hr2; [exact Hr0 | intros X; apply in_app_or in X; destruct X as [X|X]; exact (Hn X)]|].
  split; [exact Hf2|]. split; [exact Hp2|]. split; [exact Hio2|]. split; [exact Hmo2|]. split; [exact Hm2|].
  exact HR2.
Qed.

(* ======================================== the block lemma ======================================== *)
Theorem w6_c2h : w6_c2h_stmt B MT.
Proof using MTL LAWS.
unfold w6_c2h_stmt, w6_case_head_stmt. cbv beta iota.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb r Hctx Hin Hra.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & HR).
destruct Hin as (H9 & H18 & H25 & H24 & H14 & H15 & Hvb & Hvbr & Hc1 & Hg & Hrain & Hc0 & Hcr & Ham & Hdis).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_val as (Hac & _).
unfold T_SEG_STK, ASTACK in HspR, Hdis.
assert (HRb : 0 <= R /\ R + 0x1e0 <= 2 ^ 47) by lia.
clear Hsp0al Hceil Hslo Hshi H47 Hac.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
destruct r as [|b r'].
- (* no byte left: m = 0 *)
  cbn [Cursor.fuzz_u8 fst snd Z.odd length Nat.sub].
  assert (E9 : ew (Ereg regs (c2_extra0 vb)) 9 = Z_to_bv 64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E18 : ew (Ereg regs (c2_extra0 vb)) 18 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E32 : ew (Ereg regs (c2_extra0 vb)) 32 = Z_to_bv 64 vb) by exact (ew_Ereg_extra regs _ 0).
  assert (HS : st_ok rsegs (Ereg regs (c2_extra0 vb)) c2_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 W6_D2) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor]. unfold region_ok, c2_s1_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ _ 0xe8 8 (SOff 32 0) vb);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hvb].
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - unfold facts_ok. cbn [c2_facts0 c2_shf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I]. split; [|exact I].
      apply (c2_af _ _ _ _ _ _ E18); unfold SHADOW_OFF; [lia | lia | reflexivity | lia]. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (24%bv : bv 5) 0 HS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H24; reflexivity)) as HS1.
  clear HS. rename HS1 into HS.
  assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs (c2_extra0 vb)) (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs (c2_extra0 vb)) (Ereg regs (c2_extra0 vb))) by apply env_agree_refl.
  unfold cfg_at. change (w64 W6_D2) with (Z_to_bv 64 W6_D2).
  aj_run_to_tok w6_tbl_ok HS HJ SHOK c2_Bspan C2_IDX; [awr_ok_tac|].
  c2_keep.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 C2_IDX) mm (seg_rom rsegs)) md) with (cfg_at rsegs C2_IDX rg mm md) end.
  eapply (c2_chain STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ _ _ C2_IDX W6_T2
    [10; 11; 12; 13; 22; 25]%bv [10; 12; 13]%bv _
    (fun regs2 => exists v, getr regs2 12 = w64 v /\ v mod 2 ^ 32 = w6_int_even 0 mod 2 ^ 32)).
  + (* s8 was pinned to the literal it holds *)
    intros r0 Hr0 Hn. destruct (bv_eqb r0 24%bv) eqn:Hq.
    * apply bv_eqb_eq in Hq. subst r0. c2_regv HS (24%bv : bv 5). rewrite H24. reflexivity.
    * apply (regs_kept_of_st_ok rsegs _ _ _ regs (c2_extra0 vb) (w_H W) ([10; 11; 12; 13; 22; 25] ++ [24])%bv HS);
        [env_agree_chain HAE | vm_compute; reflexivity | exact Hr0 |].
      intros X. apply in_app_or in X. destruct X as [X|[X|[]]]; [exact (Hn X)|].
      rewrite <- X in Hq. vm_compute in Hq. discriminate Hq.
  + c2_kio.
  + exact KE.
  + intros x Hx. exact Hx.
  + intros x Hx. cbn [In] in Hx |- *. tauto.
  + intros regs2 (v & Hv & Hvm) Hk2.
    split; [exists v; split; [exact Hv | exact Hvm]|].
    rewrite !Hk2 by first [apply c2_nz; reflexivity | apply c2_notin; reflexivity].
    split; [c2_regv HS (11%bv : bv 5); reflexivity|].
    split.
    * (* s9 = c + 0 *)
      c2_regv HS (25%bv : bv 5). rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl), H25. unfold w64.
      rewrite unsigned_lit_small by lia. f_equal; lia.
    * c2_regv HS (22%bv : bv 5). rewrite E32, unsigned_lit_small by lia. unfold w64. f_equal; lia.
  + apply (c2_int_block STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k _ 0 HJ).
    * exact (c2_rom_eq W W memc _ KE HR).
    * exact (c2_ra_eq _ _ _ _ _ KE Hra).
    * c2_regv HS (12%bv : bv 5). reflexivity.
    * lia.
    * c2_regv HS (18%bv : bv 5). rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- (* a byte m = b, the rest r' *)
  cbn [Cursor.fuzz_u8 fst snd].
  pose proof (Cursor.byte_range b) as Hmb.
  set (m := bv_unsigned b) in *.
  set (n := Z.of_nat (length (b :: r'))) in *.
  assert (Hn : n = Z.of_nat (length r') + 1) by (subst n; cbn [length]; lia).
  assert (Hnb : 1 <= n /\ c + n <= 2 ^ 47 - 1).
  { split; [lia|]. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
  assert (Hcd : c < R + 0x60 \/ R + 0x120 <= c).
  { destruct (Hdis c ltac:(lia)) as (_ & Hd & _). lia. }
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) (c + 0) 1 m).
  { destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]. exact Hv. }
  assert (E9 : ew (Ereg regs (c2_extra1 vb m)) 9 = Z_to_bv 64 R)
    by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E14 : ew (Ereg regs (c2_extra1 vb m)) 14 = Z_to_bv 64 (c - 1))
    by (rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
  assert (E15 : ew (Ereg regs (c2_extra1 vb m)) 15 = Z_to_bv 64 (n + 1))
    by (rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
  assert (E18 : ew (Ereg regs (c2_extra1 vb m)) 18 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E24 : ew (Ereg regs (c2_extra1 vb m)) 24 = Z_to_bv 64 n)
    by (rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
  assert (E25 : ew (Ereg regs (c2_extra1 vb m)) 25 = Z_to_bv 64 c)
    by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
  assert (E32 : ew (Ereg regs (c2_extra1 vb m)) 32 = Z_to_bv 64 vb) by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs (c2_extra1 vb m)) 33 = Z_to_bv 64 m) by exact (ew_Ereg_extra regs _ 1).
  assert (HS : st_ok rsegs (Ereg regs (c2_extra1 vb m)) c2_ss1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 W6_D2) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor]].
      + unfold region_ok, c2_s1_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ _ 0xe8 8 (SOff 32 0) vb);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hvb].
      + unfold region_ok, c2_in_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E25, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ _ 0 1 (SOff 33 0) m);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | exact Hm0].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c2_s1_region, c2_in_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E25, !unsigned_lit_small by lia.
      split; [split; [lia | exact I] | split; exact I].
    - unfold facts_ok. cbn [c2_facts1 c2_shf f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I]. split; [|split; [|split; [|split; [|exact I]]]].
      + apply (c2_af _ _ _ _ _ _ E18); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
      + apply (c2_af _ _ _ _ _ _ E25); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c2_af _ _ _ _ _ _ E24); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c2_af _ _ _ _ _ _ E33); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  assert (SHOK : sh_ok rsegs c2_Bx [] (Ereg regs (c2_extra1 vb m)) (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs (c2_extra1 vb m)) (Ereg regs (c2_extra1 vb m)))
    by apply env_agree_refl.
  unfold cfg_at. change (w64 W6_D2) with (Z_to_bv 64 W6_D2).
  (* 0x816ac .. the branch on m & 1 at 0x816d4 *)
  aj_run_to_tok w6_tbl_ok HS HJ SHOK c2_Bspan C2_IDX.
  { apply (obl_of_range rsegs (w_H W) memc _ c2_Bx _ _ c n Hrain).
    - apply (U_atom _ 18 SHADOW_OFF E18). unfold SHADOW_OFF. lia.
    - rewrite (U_atom _ 25 c E25) by lia. lia.
    - rewrite (U_atom _ 25 c E25) by lia. lia. }
  { awr_ok_tac. }
  c2_keep.
  srr_branch_tok w6_tbl_ok HS SHOK c2_Bspan.
  + (* m even: to 0x819c4, then the int *)
    rewrite (c2_parity _ m) in Hc; [| rewrite ?ew_ewset_other by lia; exact E33 | exact Hmb].
    apply negb_true_iff in Hc. rewrite Hc. cbv beta iota.
    aj_run_to_tok w6_tbl_ok HS HJ SHOK c2_Bspan C2_IDX; [awr_ok_tac|].
    c2_keep.
    lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
      rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) end.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 C2_IDX) mm (seg_rom rsegs)) md) with (cfg_at rsegs C2_IDX rg mm md) end.
    eapply (c2_chain STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ _ _ C2_IDX W6_T2
      [10; 11; 12; 13; 22; 25]%bv [10; 12; 13]%bv _
      (fun regs2 => exists v, getr regs2 12 = w64 v /\ v mod 2 ^ 32 = w6_int_even m mod 2 ^ 32)).
    * eapply (regs_kept_of_st_ok rsegs _ _ _ regs (c2_extra1 vb m) (w_H W) _ HS);
        [env_agree_chain HAE | vm_compute; reflexivity].
    * c2_kio.
    * exact KE.
    * intros x Hx. exact Hx.
    * intros x Hx. cbn [In] in Hx |- *. tauto.
    * intros regs2 (v & Hv & Hvm) Hk2.
      split; [exists v; split; [exact Hv | exact Hvm]|].
      rewrite !Hk2 by first [apply c2_nz; reflexivity | apply c2_notin; reflexivity].
      split; [c2_regv HS (11%bv : bv 5); rewrite E15, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
      split; [c2_regv HS (25%bv : bv 5); rewrite E14, unsigned_lit_small by lia; unfold w64; f_equal; cbn [length]; lia|].
      c2_regv HS (22%bv : bv 5). rewrite E32, unsigned_lit_small by lia. unfold w64. f_equal; lia.
    * apply (c2_int_block STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k _ m HJ).
      -- exact (c2_rom_eq W W memc _ KE HR).
      -- exact (c2_ra_eq _ _ _ _ _ KE Hra).
      -- c2_regv HS (12%bv : bv 5). rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- exact Hmb.
      -- c2_regv HS (18%bv : bv 5). rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + (* m odd: to 0x816d8 *)
    rewrite (c2_parity _ m) in Hc; [| rewrite ?ew_ewset_other by lia; exact E33 | exact Hmb].
    apply negb_false_iff in Hc. rewrite Hc. cbv beta iota.
    aj_run_to_tok w6_tbl_ok HS HJ SHOK c2_Bspan W6_U2; [awr_ok_tac|].
    c2_keep.
    c2_leaf HAE idtac.
    split; [c2_regv HS (11%bv : bv 5); rewrite E15, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    split; [c2_regv HS (12%bv : bv 5); rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [c2_regv HS (25%bv : bv 5); rewrite E14, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
    c2_regv HS (22%bv : bv 5). rewrite E32, unsigned_lit_small by lia. unfold w64. f_equal; lia.
Qed.

End d.
End b.

Print Assumptions w6_c2h.
