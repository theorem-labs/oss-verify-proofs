(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgDcsvBody.v at 693242f63d54 for image B (fuzz_rate.asan-ubsan): image B's pcs, cells, registers and block boundaries against lib/AU/RtPgDcsvDefsB.v; the B-only steps (s4 := ~tmp, a2 from s9, the two pointer-overflow trap branches 0x84508 and 0x84520, decided by the engine from atom range facts) added to blocks C1, C2 and C3. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address below is measured on its
   unstripped twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded bytes are
   the same): PART 2 of the walk of reac_rate_drivable_csv (0x842d8, 1056 bytes, 264 instructions), one pass of its
   loop, from the head 0x84478 to the next pass's head (i = 0, 1) or to the tail 0x8457c (i = 2), against
   lib/AU/RtPgDcsvDefsB.v dc_body_stmt. Proves no function (kind: segment lemma, one pass of the loop).

   The pass is run in blocks, each from a fresh symbolic state built from the cut state's facts:
     A  0x84478 .. 0x844c0, stops at the `beqz a0` 0x844c4 (the token engine, lib/Reusable/YCbn.v): the
        instrumented check of the 4-byte read of ordered[i] (s7 = s10 = 0x216a0 + 4 i is one atom, the shadow
        offset is the env slot 32 the cell R+88 holds, no shadow entry: the engine leaves the obligation that the
        4 bytes at ordered + 4 i are marked usable, which rt_i32tab gives; the slow block 0x84568 .. 0x84570 and
        the error path call 0x84578 are never stepped); `lw a4,0(s7)` reads the literal ordered[i]; the compare
        chain gives a0 = rate_bit ordered[i]; `and a0,a0,a1` with the mask atom.
     B  the bit clear (a0 = 0): 0x844c4 -> 0x84554 .. 0x84560 (0x84564 for i = 2) -> the head or the tail.
     C1 the bit set: 0x844c4 .. 0x844ec, s4 := a3 (~tmp), the two shadow stores of cell, the separator split on
        len = 0 (`beqz s5`), a0 := cell (R+72), a2 := the format (s9), the call `jal 0x4222c`; stops at the snprintf
        wrapper's trampoline with ra = 0x844f0.
     the snprintf wrapper (RtPgDcsvDefsB.v rate_snprintf_sd_realizes), at a new float state.
     C2 0x844f0 .. 0x84518: `bltz a0` and `bltu 31,s3` decided from the ranges (|T| is 5 or 6, len <= 17);
        a3 := s4; THE TRAP BRANCH 0x84508 `bltu a3,s5` (to the `unimp` 0x846e8) decided not taken by the engine
        alone, from the range [2^63, 2^64 - 1] of s4's atom (~tmp = 2^64 - 1 - (F + 32), F + 128 <= 2^47) and the
        range of s5 (the literal 0, or [1, 17]); the call `jal 0x518b8` (__asan_memcpy(tmp + len, cell, |T|)),
        ra = 0x8451c.
     __asan_memcpy (YG0d.v aintrin_realizes OCpy).
     C3 0x8451c .. 0x84560: THE TRAP BRANCH 0x84520 `bltu s4,s3` decided not taken by the engine alone, from the
        range of s4's atom and the range [0, 23] of s3's (len + |T|); a3 := s4 (the next head's ~tmp); the NUL at
        tmp + len + |T| (the store has no instrumented check), the two shadow bytes of cell back to 0xf8,
        len := len + |T|, then as B.
   Every byte a pass writes is in tmp or cell (the class-1 frame, which the runtime owned at the call: YF0v
   own_free_frame), in the two shadow bytes of cell (written back to their value), or in the callees' stack windows
   below the realigned sp R (inside [S - T_dcsv_STK, S)). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YImgTop YF0v YG0s YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgSiteB RtPgDcsvDefsB RtPgStepsB RtPgMemB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the engine's context ======================================== *)
(* env slot 32 is the runtime's shadow offset, the base of the token engine's shadow address *)
Definition DCBx : sv := SOff 32 0.
Definition DCspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* the three values of ordered and their bits *)
Definition dc_v (i : nat) : Z := nth i RateCfg.closed_list 0.
Definition dc_bit (i : nat) : Z := RateCfg.rate_bit (dc_v i).
Lemma dc_v_range : forall i, (i < 3)%nat -> 0 < dc_v i < 2 ^ 31.
Proof. intros i Hi. destruct i as [|[|[|i]]]; [| | |lia]; vm_compute; split; reflexivity. Qed.

(* every byte is kept by a run whose regions have no write window *)
Lemma dc_kept_nowin : forall E (rs : smem) (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
  forall a, aview rsegs H m' a = aview rsegs H m a.
Proof.
  intros E rs H m m' HF Hro a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & Hr). pose proof (proj1 (Forall_forall _ _) Hro r Hin) as Hw. cbv beta in Hw.
  revert Hr Hw. generalize (bv_unsigned (Z_to_bv 64 a)) (base_val E (YP09.r_base r)) (YP09.r_wlo r) (YP09.r_whi r).
  intros. lia.
Qed.

(* ======================================== the post of a block ======================================== *)
Section post. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* A block ends at pc with the same layout, state and world (no call into the model), every register outside clob
   as at its start, every byte outside Wr as at its start, every present byte present, and R. *)
Definition dcb_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (lyc : alayout) (S1 : astate)
  (W1 : world rsegs) (regsA : bvmap 5 word) (memA : word -> option byte) (mdA : Model)
  (pc : Z) (clob : list (bv 5)) (Wr : Z -> Prop) (R : bvmap 5 word -> (word -> option byte) -> Prop)
  : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W1 /\ exists regs2 mem2 md2,
  c2 = cfg_at rsegs pc regs2 mem2 md2 /\
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem2 md2 k /\
  (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regsA r) /\
  same_io mdA md2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W1) memA a) /\
  (forall a, apresent (w_H W1) memA a -> apresent (w_H W1) mem2 a) /\
  R regs2 mem2.
End post.

(* ======================================== block A ======================================== *)
(* the real frame's cells the block reads: R+56 = 48000, R+80 = the mask (env slot 33), R+88 = the shadow offset *)
Definition dcA_frame : YP09.region :=
  YP09.mkRegion (Some 9%nat) 56 96 0 0
   [YP09.mkChunk 56 (CVal 8 (SLit 48000)); YP09.mkChunk 80 (CVal 8 (SOff 33 0)); YP09.mkChunk 88 (CVal 8 (SOff 32 0))].
(* ordered[i], at the atom of s7 *)
Definition dcA_tab (i : nat) : YP09.region :=
  YP09.mkRegion (Some 23%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit (dc_v i)))].
Definition dcA_facts (i : nat) : facts :=
  mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (23%nat, mkAF (B_ORD + 4 * Z.of_nat i) (B_ORD + 4 * Z.of_nat i) 2)] [] [].
Definition dcA_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms (22%bv : bv 5) (SLit 44100)) (24%bv : bv 5) (SLit 96000)) (26%bv : bv 5) (SOff 23 0).
Definition dcA_ss (i : nat) : sstate := mkSS DC_LOOP dcA_regs [dcA_frame; dcA_tab i] None (dcA_facts i).
Definition dcA_extra (mask : Z) : list word := [w64 SHADOW_OFF; w64 mask].

Section blkA. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma dcA_entry : forall (W : world rsegs) regs mem (i : nat) R mask,
  (i < 3)%nat ->
  getr regs 9 = w64 R -> getr regs 22 = w64 44100 -> getr regs 24 = w64 96000 ->
  getr regs 23 = w64 (B_ORD + 4 * Z.of_nat i) -> getr regs 26 = w64 (B_ORD + 4 * Z.of_nat i) ->
  2 ^ 46 <= R -> R + 224 <= 2 ^ 47 -> 0 <= mask < 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W) mem) (R + 56) 8 48000 ->
  val_mem rsegs (mrestrict (w_H W) mem) (R + 80) 8 mask ->
  val_mem rsegs (mrestrict (w_H W) mem) (R + 88) 8 SHADOW_OFF ->
  rt_i32tab rsegs (w_H W) mem B_ORD RateCfg.closed_list ->
  st_ok rsegs (Ereg regs (dcA_extra mask)) (dcA_ss i)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 DC_LOOP) mem (seg_rom rsegs))).
Proof.
  intros W regs mem i R mask Hi H9 H22 H24 H23 H26 HR0 HR1 Hm V56 V80 V88 Htab.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs (dcA_extra mask)).
  pose proof shadow_off_range as Hso.
  assert (Hord : 0 <= B_ORD + 4 * Z.of_nat i < 2 ^ 64) by (unfold B_ORD; lia).
  assert (E9 : bv_unsigned (ew E 9) = R)
    by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (E23 : bv_unsigned (ew E 23) = B_ORD + 4 * Z.of_nat i)
    by (subst E; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl), H23; apply unsigned_lit_small; exact Hord).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 mask) by (subst E; exact (ew_Ereg_extra regs _ 1)).
  assert (Hv : 0 < dc_v i < 2 ^ 31) by (apply dc_v_range; exact Hi).
  destruct Htab as (_ & _ & Hvals & _).
  assert (Vt : val_mem rsegs (mrestrict (w_H W) mem) (B_ORD + 4 * Z.of_nat i + 0) 4 (dc_v i)).
  { rewrite Z.add_0_r. pose proof (Hvals (Z.of_nat i) ltac:(change (length RateCfg.closed_list) with 3%nat; lia)) as V.
    rewrite Nat2Z.id in V. exact V. }
  assert (HS0 : st_ok rsegs E (mkSS DC_LOOP sr_atoms [dcA_frame; dcA_tab i] None (dcA_facts i))
    (mkst regs (Z_to_bv 64 DC_LOOP) (mrestrict (w_H W) mem) (seg_rom rsegs))).
  { subst E. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - destruct i as [|[|[|i]]]; [| | |lia]; vm_compute; reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (rtmb_ro_region rsegs _ _ _ 9 R); [exact E9 | lia | lia |].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        * apply (chunk_ok_val rsegs _ _ R 56 8 (SLit 48000) 48000); [reflexivity | cbn; lia | lia | exact V56].
        * apply (chunk_ok_val rsegs _ _ R 80 8 (SOff 33 0) mask); [|cbn; lia | lia | exact V80].
          apply bv_eq. rewrite denot_SOff, E33, Z.add_0_r, unsigned_lit_small by lia.
          apply zcanon_id. unfold M64. lia.
        * apply (chunk_ok_val rsegs _ _ R 88 8 (SOff 32 0) SHADOW_OFF); [|cbn; lia | lia | exact V88].
          apply bv_eq. rewrite denot_SOff, E32, Z.add_0_r, unsigned_lit_small by lia.
          apply zcanon_id. unfold M64. lia.
      + apply (rtmb_ro_region rsegs _ _ _ 23 (B_ORD + 4 * Z.of_nat i)); [exact E23 | lia | unfold B_ORD; lia |].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs _ _ _ 0 4 (SLit (dc_v i)) (dc_v i));
          [reflexivity | change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia | lia | exact Vt].
    - apply pairwise_disjoint_of_extents. unfold dcA_frame, dcA_tab, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E23.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold B_ORD. repeat split; lia.
    - split; [|split; [exact I | exact I]]. cbn [dcA_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, E23, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. change (2 ^ 2) with 4.
      unfold B_ORD. repeat split; try lia; apply Z.mod_divide; try lia; exists (34216 + Z.of_nat i); lia. }
  pose proof (st_ok_pin_lit rsegs E _ _ (22%bv : bv 5) 44100 HS0 eq_refl H22) as HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
  pose proof (st_ok_pin_lit rsegs E _ _ (24%bv : bv 5) 96000 HS1 eq_refl H24) as HS2.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  pose proof (st_ok_pin_sv rsegs E _ _ (26%bv : bv 5) (SOff 23 0) HS2 eq_refl
    ltac:(cbn [ms_regs mkst]; apply bv_eq; rewrite denot_SOff, Z.add_0_r, E23, H26;
          rewrite unsigned_lit_small by exact Hord; apply zcanon_id; unfold M64; lia)) as HS3.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
  exact HS3.
Qed.
End blkA.

(* ======================================== the leaf of a block ======================================== *)
Section den. Context {fx : YK11.FPState}.
Lemma dc_den_and : forall E n m b, ew E n = Z_to_bv 64 m -> 0 <= m < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n 0) (SLit b)) = w64 (Z.land b m).
Proof.
  intros E n m b Hn Hm Hb. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu, U_SLit, (U_atom E n m Hn Hm). cbn [zalu_raw]. rewrite (zcanon_id b) by (unfold M64; lia).
  rewrite Z.land_comm. pose proof (Z_land_upper b m ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.
Lemma dc_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = w64 v.
Proof. intros E n v H Hv. exact (rtsb_den_atom E n v H Hv). Qed.
End den.

(* the value of a register in the run's final state, as the sv the engine computed *)
Ltac dc_sv HSx :=
  lazymatch goal with |- getr _ _ = _ => rewrite (st_ok_restrict_reg rsegs _ _ _ _ _ HSx) | _ => idtac end;
  match goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
(* an env slot below the token atoms, through the run's env extensions *)
Ltac dc_ew := rewrite ?ew_ewset_other by lia.
(* the post of a block from the run's final state: pins (register, sv) the entry state set, pintac proves their
   values, memtac the memory clause, Rtac the block's own clause from the final state HS *)
Ltac dcb_leaf regs0 extra0 pins pintac memtac Rtac :=
lazymatch goal with
| HS : st_ok _ ?Ex ?ssf (restrict (w_H ?Wx) ?msx),
  HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HGx : mem_grows _ _ |- _ =>
  apply SRr_ret; split; [reflexivity|];
  exists (ms_regs msx), (ms_mem msx); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H Wx) Ex ssf msx HS eq_refl) at 1; reflexivity|];
  split; [exact HJx|];
  split; [eapply (regs_kept_of_st_ok_pins rsegs Ex ssf msx regs0 extra0 (w_H Wx) _ pins HS);
          [ split; [intros n0 Hn0; dc_ew; reflexivity | reflexivity]
          | pintac
          | vm_compute; reflexivity ]|];
  split; [first [apply same_io_refl | apply same_io_wvb]|];
  split; [memtac|];
  split; [let a := fresh "a" in intros a; apply apresent_grows; exact HGx|];
  Rtac HS
end.
(* a block whose regions have no write window keeps every byte *)
Ltac dc_mem_nowin :=
  let a := fresh "a" in intros a _ _;
  eapply dc_kept_nowin; [eassumption|];
  cbn [ss_mem]; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.

(* the literal bit of a `Z.land b x` clause, computed *)
Ltac dc_vm_land :=
  lazymatch goal with |- _ = w64 (Z.land ?b _) => let b' := eval vm_compute in b in change b with b' end.

(* ======================================== block A ======================================== *)
Ltac dcA_run HS HJ SHOK E23 E32 E33 Hra Hso H22 H24 H26 regs extra :=
  aj_run_tok dc_tbl_ok HS HJ SHOK DCspan;
  [ (* the obligation: the 4 bytes of ordered[i] are marked usable *)
    unfold DCBx; rewrite (U_atom _ 32 SHADOW_OFF E32 Hso);
    rewrite (U_atom _ 23 _ E23) by (unfold B_ORD; lia);
    eapply ra_sub; [exact Hra | unfold B_ORD; lia | unfold B_ORD; lia]
  | awr_ok_tac
  | dcb_leaf regs extra [((22%bv : bv 5), SLit 44100); ((24%bv : bv 5), SLit 96000); ((26%bv : bv 5), SOff 23 0)]
      ltac:(let rr := fresh "rr" in let ee := fresh "ee" in let Hin := fresh "Hin" in
            intros rr ee Hin; destruct Hin as [Hq|[Hq|[Hq|[]]]]; injection Hq as <- <-;
            [ cbn [sv_denot]; rewrite H22; reflexivity
            | cbn [sv_denot]; rewrite H24; reflexivity
            | rewrite H26; apply dc_den_atom; [dc_ew; exact E23 | unfold B_ORD; lia] ])
      dc_mem_nowin
      ltac:(fun HSf => split; [dc_sv HSf; dc_vm_land; apply dc_den_and; [dc_ew; exact E33 | lia | lia]|];
                       split; [dc_sv HSf; apply dc_den_atom; [dc_ew; exact E33 | lia]|];
                       dc_sv HSf; reflexivity) ].

Section blkA2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Definition dcA_R (i : nat) (mask : Z) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 _ => getr regs2 10 = w64 (Z.land (dc_bit i) mask) /\ getr regs2 11 = w64 mask /\ getr regs2 14 = w64 (dc_v i).
Lemma dcb_A : forall STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md (i : nat) R mask,
  (i < 3)%nat ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem md k ->
  getr regs 9 = w64 R -> getr regs 22 = w64 44100 -> getr regs 24 = w64 96000 ->
  getr regs 23 = w64 (B_ORD + 4 * Z.of_nat i) -> getr regs 26 = w64 (B_ORD + 4 * Z.of_nat i) ->
  2 ^ 46 <= R -> R + 224 <= 2 ^ 47 -> 0 <= mask < 2 ^ 64 ->
  val_mem rsegs (mrestrict (w_H W1) mem) (R + 56) 8 48000 ->
  val_mem rsegs (mrestrict (w_H W1) mem) (R + 80) 8 mask ->
  val_mem rsegs (mrestrict (w_H W1) mem) (R + 88) 8 SHADOW_OFF ->
  rt_i32tab rsegs (w_H W1) mem B_ORD RateCfg.closed_list ->
  SRr rsegs W1 (cfg_at rsegs DC_LOOP regs mem md)
    (dcb_post B STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md 0x844c4 [10; 11; 14]%bv
       (fun _ => False) (dcA_R i mask)).
Proof using LAWS.
  intros STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md i R mask
    Hi HJ H9 H22 H24 H23 H26 HR0 HR1 Hm V56 V80 V88 Htab.
  pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs. pose proof shadow_off_range as Hso.
  pose proof (dcA_entry W1 regs mem i R mask Hi H9 H22 H24 H23 H26 HR0 HR1 Hm V56 V80 V88 Htab) as HS.
  destruct Htab as (_ & _ & _ & Hra). change (length RateCfg.closed_list) with 3%nat in Hra.
  assert (E23 : ew (Ereg regs (dcA_extra mask)) 23 = Z_to_bv 64 (B_ORD + 4 * Z.of_nat i))
    by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
  assert (E32 : ew (Ereg regs (dcA_extra mask)) 32 = Z_to_bv 64 SHADOW_OFF) by exact (ew_Ereg_extra regs _ 0).
  assert (E33 : ew (Ereg regs (dcA_extra mask)) 33 = Z_to_bv 64 mask) by exact (ew_Ereg_extra regs _ 1).
  assert (SHOK : sh_ok rsegs DCBx [] (Ereg regs (dcA_extra mask)) (mrestrict (w_H W1) mem)) by constructor.
  unfold cfg_at. change (w64 DC_LOOP) with (Z_to_bv 64 DC_LOOP).
  destruct i as [|[|[|i]]]; [| | | lia];
  dcA_run HS HJ SHOK E23 E32 E33 Hra Hso H22 H24 H26 regs (dcA_extra mask).
Qed.
End blkA2.

(* ======================================== block B: the bit clear ======================================== *)
(* 0x844c4 `beqz a0` taken (a0 = 0); 0x84554 .. 0x8455c s11 := 2 - i, s10 := s7 := ordered + 4 (i + 1);
   0x84560 `bnez s11` back to the head (i = 0, 1) or 0x84564 `j 0x8457c` (i = 2) *)
Definition dcB_stop (i : nat) : Z := match i with 2%nat => DC_TAIL | _ => DC_LOOP end.
Definition dcB_ss (i : nat) : sstate :=
  mkSS 0x844c4 (sr_set (sr_set (sr_set (sr_set sr_atoms (10%bv : bv 5) (SLit 0)) (27%bv : bv 5) (SLit (3 - Z.of_nat i)))
    (23%bv : bv 5) (SLit (B_ORD + 4 * Z.of_nat i))) (26%bv : bv 5) (SLit (B_ORD + 4 * Z.of_nat i)))
    [] None (mkFacts [] [] []).
Definition dcB_R (i : nat) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 _ => getr regs2 27 = w64 (3 - Z.of_nat (S i)) /\
    getr regs2 23 = w64 (B_ORD + 4 * Z.of_nat (S i)) /\ getr regs2 26 = w64 (B_ORD + 4 * Z.of_nat (S i)).
(* an entry state with no region and no fact, the listed registers pinned to the literals they hold *)
Section blkB. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma dcB_entry : forall (W : world rsegs) regs mem (i : nat),
  getr regs 10 = w64 0 -> getr regs 27 = w64 (3 - Z.of_nat i) ->
  getr regs 23 = w64 (B_ORD + 4 * Z.of_nat i) -> getr regs 26 = w64 (B_ORD + 4 * Z.of_nat i) ->
  st_ok rsegs (Ereg regs []) (dcB_ss i) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x844c4) mem (seg_rom rsegs))).
Proof.
  intros W regs mem i H10 H27 H23 H26. rewrite restrict_mkst_fx.
  assert (HS0 : st_ok rsegs (Ereg regs []) (mkSS 0x844c4 sr_atoms [] None (mkFacts [] [] []))
    (mkst regs (Z_to_bv 64 0x844c4) (mrestrict (w_H W) mem) (seg_rom rsegs))).
  { apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - reflexivity.
    - apply Forall_nil.
    - exact I.
    - split; [exact I | split; exact I]. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) 0 HS0 eq_refl H10) as HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
  pose proof (st_ok_pin_lit rsegs _ _ _ (27%bv : bv 5) _ HS1 eq_refl H27) as HS2.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  pose proof (st_ok_pin_lit rsegs _ _ _ (23%bv : bv 5) _ HS2 eq_refl H23) as HS3.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
  pose proof (st_ok_pin_lit rsegs _ _ _ (26%bv : bv 5) _ HS3 eq_refl H26) as HS4.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4.
  exact HS4.
Qed.
End blkB.

Definition dcB_pins (i : nat) : list (bv 5 * sv) :=
  [((10%bv : bv 5), SLit 0); ((27%bv : bv 5), SLit (3 - Z.of_nat i)); ((23%bv : bv 5), SLit (B_ORD + 4 * Z.of_nat i));
   ((26%bv : bv 5), SLit (B_ORD + 4 * Z.of_nat i))].
(* the pins of an entry state that sets registers to literals: each pinned value is the hypothesis' *)
Ltac dc_pins_lit :=
  let rr := fresh "rr" in let ee := fresh "ee" in let Hin := fresh "Hin" in
  intros rr ee Hin;
  repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- <-; cbn [sv_denot]; symmetry; assumption|]);
  destruct Hin.
Ltac dcB_run HS HJ regs :=
  lazymatch goal with |- context [dcB_stop ?j] => let st := eval vm_compute in (dcB_stop j) in
    aj_run_to dc_tbl_ok HS HJ st;
    [ awr_ok_tac
    | dcb_leaf regs (@nil word) (dcB_pins j) dc_pins_lit dc_mem_nowin
        ltac:(fun HSf => split; [dc_sv HSf; reflexivity|]; split; [dc_sv HSf; reflexivity|]; dc_sv HSf; reflexivity) ]
  end.

Section blkB2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Lemma dcb_B : forall STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md (i : nat),
  (i < 3)%nat ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem md k ->
  getr regs 10 = w64 0 -> getr regs 27 = w64 (3 - Z.of_nat i) ->
  getr regs 23 = w64 (B_ORD + 4 * Z.of_nat i) -> getr regs 26 = w64 (B_ORD + 4 * Z.of_nat i) ->
  SRr rsegs W1 (cfg_at rsegs 0x844c4 regs mem md)
    (dcb_post B STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md (dcB_stop i) [23; 26; 27]%bv
       (fun _ => False) (dcB_R i)).
Proof using LAWS.
  intros STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md i Hi HJ H10 H27 H23 H26.
  pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
  pose proof (dcB_entry W1 regs mem i H10 H27 H23 H26) as HS.
  unfold cfg_at. change (w64 0x844c4) with (Z_to_bv 64 0x844c4).
  destruct i as [|[|[|i]]]; [| | | lia]; dcB_run HS HJ regs.
Qed.
End blkB2.

(* ======================================== the cut state over a pass ======================================== *)
Ltac dc_num := unfold shadow_addr, shadow_of_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd, kLowMemEnd,
  ASAN_CEIL, ESTACK, T_dcsv_STK, DC_FSZ in *; lia.
(* a cell of the real frame, kept: its 8 bytes are outside the pass's writes *)
Ltac dc_vk W1 mem1 mem2 KEEP :=
  apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 mem2); [let kk := fresh "kk" in let Hkk := fresh "Hkk" in
    intros kk Hkk; apply KEEP; cbn in Hkk; dc_num | assumption].

Section carry. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis IMG : rate_B_img_facts rsegs B.
(* dc_core holds again after a pass that keeps the state, the world and the registers the tail reads, writes only
   tmp, cell and the stack below R, and leaves in tmp the prefix of i' passes *)
Lemma dc_carry : forall (c : dcx) (i i' : nat) pos (fq fq' : YK11.FPState) S1 W1 regs1 mem1 md1 regs2 mem2 md2,
  @dc_pre fx rc SK B c -> @dc_core fx rc SK B c i pos fq S1 W1 regs1 mem1 md1 ->
  (i' <= 3)%nat -> rt_fxk [10] fx fq' ->
  ajournal rsegs B (dx_STK c) (dx_sp0 c) (dx_FP c) (dx_ly c) (dx_S c) (dx_W0 c) (dx_mem0 c) (dx_md0 c)
    ((DC_CID, pos) :: dx_own c) (dx_lyc c) S1 W1 mem2 md2 (dx_k c) ->
  same_io md1 md2 ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (frame_addr (dx_lyc c) DC_CID pos + 32 <= a < frame_addr (dx_lyc c) DC_CID pos + 64) ->
     ~ (frame_addr (dx_lyc c) DC_CID pos + 96 <= a < frame_addr (dx_lyc c) DC_CID pos + 112) ->
     ~ (dx_R c - 2 * ESTACK <= a < dx_R c) ->
     aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W1) mem1 a) ->
  (forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) mem2 a) ->
  getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
  getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
  getr regs2 21 = w64 (Z.of_nat (length (RateCsv.csv_prefix (dx_mask c) i'))) ->
  garr8 rsegs (mrestrict (w_H W1) mem2) (frame_addr (dx_lyc c) DC_CID pos + 32)
    (RateCsv.csv_prefix (dx_mask c) i' ++ [0]) ->
  @dc_core fx rc SK B c i' pos fq' S1 W1 regs2 mem2 md2.
Proof using LAWS IMG.
  intros c i i' pos fq fq' S1 W1 regs1 mem1 md1 regs2 mem2 md2 Hpre HC Hi' Hfx HJ2 Hio2 Hk Hpr
    R2 R3 R4 R8 R9 R18 R21 Htmp.
  destruct Hpre as (Hcpre & _ & _ & _ & _ & Hn & Hbufpre & _).
  destruct Hcpre as (HJc & _ & _ & _ & _ & _ & Hwin & Hwin2 & _).
  unfold dc_core in HC |- *. cbv zeta in HC |- *.
  destruct HC as (Hi & Hfx0 & HJ & Hfr & Hnin & Hfs & Hpos & Hab & Hnev & Hsecs & Hch & Hio & Hwle & HRm & HRr &
    G2 & G3 & G4 & G8 & G9 & G18 & G21 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V112 &
    Vsav & Hflag & _ & Hsh & HpF & HpS & Cfmt & Ccom & Cemp & Ctab & Hrom & Hbuf & Hkept).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof (proj1 HJ2) as HAR2.
  pose proof ASAN_CEIL_range as Hcr. pose proof asan_consts as (C1 & _).
  change (spZ (dx_regs c)) with (dx_S0 c) in Hwin, Hwin2.
  assert (Hin1 : In (DC_CID, pos) (frames S1)) by (rewrite Hfr; left; reflexivity).
  destruct (frames_bounds rsegs B LAWS (dx_lyc c) S1 W1 mem2 md2 DC_CID pos HAR2 Hin1) as (HF0 & HFc & HFapp).
  change (fs_frame_bytes DC_CID) with 128 in HFc, HFapp.
  set (F := frame_addr (dx_lyc c) DC_CID pos) in *.
  set (R := dx_R c) in *. set (S0 := dx_S0 c) in *.
  unfold in_app in HFapp.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> (a < F + 32 \/ F + 64 <= a) -> (a < F + 96 \/ F + 112 <= a) ->
    (a < R - 2 * ESTACK \/ R <= a) -> aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W1) mem1 a).
  { intros a Ha H1 H2 H3. apply Hk; [exact Ha | lia | lia | lia]. }
  assert (HRw : alloc_ceiling <= R - 2 * ESTACK) by (unfold T_dcsv_STK in Hwin; unfold ESTACK in *; lia).
  (* the frame bytes are not image bytes *)
  assert (NIMG : forall a, F <= a < F + 128 -> ~ in_img rsegs a).
  { intros a Ha. apply (proj2 (al_client_img _ _ LAWS (dx_lyc c) S1 W1 mem2 md2 a HAR2
      (or_intror (or_introl (ex_intro _ DC_CID (ex_intro _ pos (conj Hin1 Ha))))))). }
  (* the image's strings and table, rebuilt at the end state from the head's: the pass writes no image byte *)
  assert (KI : forall a, in_img rsegs a -> ~ Exists (in_zr a) (as_owned_static B) ->
    aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W1) mem1 a).
  { intros a Hai _. pose proof (rtsb_segs_low a Hai) as Hlow.
    assert (NF : ~ (F <= a < F + 128)) by (intros Hx; exact (NIMG a Hx Hai)).
    apply KEEP; dc_num. }
  destruct (dc_img_carry_from B IMG (w_H W1) mem1 (dx_lyc c) S1 W1 mem2 md2 Cfmt Ccom Cemp Ctab HAR2 KI)
    as (I1 & I2 & I3 & I4).
  refine (conj Hi' (conj Hfx (conj HJ2 _))).
  repeat match goal with |- _ /\ _ => split end.
  - exact Hfr.
  - exact Hnin.
  - exact Hfs.
  - lia.
  - lia.
  - exact Hab.
  - exact Hnev.
  - exact Hsecs.
  - exact Hch.
  - eapply same_io_trans; eassumption.
  - exact Hwle.
  - exact HRm.
  - lia.
  - lia.
  - rewrite R2; exact G2.
  - rewrite R3; exact G3.
  - rewrite R4; exact G4.
  - rewrite R8; exact G8.
  - rewrite R9; exact G9.
  - rewrite R18; exact G18.
  - exact R21.
  - dc_vk W1 mem1 mem2 KEEP.
  - dc_vk W1 mem1 mem2 KEEP.
  - dc_vk W1 mem1 mem2 KEEP.
  - dc_vk W1 mem1 mem2 KEEP.
  - dc_vk W1 mem1 mem2 KEEP.
  - dc_vk W1 mem1 mem2 KEEP.
  - dc_vk W1 mem1 mem2 KEEP.
  - dc_vk W1 mem1 mem2 KEEP.
  - dc_vk W1 mem1 mem2 KEEP.
  - dc_vk W1 mem1 mem2 KEEP.
  - dc_vk W1 mem1 mem2 KEEP.
  - dc_vk W1 mem1 mem2 KEEP.
  - intros j Hj. apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 mem2); [| apply Vsav; exact Hj].
    intros kk Hkk. apply KEEP; cbn in Hkk; dc_num.
  - rewrite <- Hflag. apply rdword_ext. intros kk Hkk. apply KEEP; dc_num.
  - exact Htmp.
  - apply (rtmb_fsh_kept rsegs (w_H W1) mem1 (w_H W1) mem2 F dc_shA Hsh).
    intros j Hj. change (length dc_shA) with 16%nat in Hj. apply KEEP; dc_num.
  - intros a Ha. apply Hpr. apply HpF. exact Ha.
  - intros a Ha. apply Hpr. apply HpS. exact Ha.
  - exact I1.
  - exact I2.
  - exact I3.
  - exact I4.
  - intros a Ha Ho He.
    assert (Hai : in_img rsegs a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
    pose proof (rtsb_segs_low a Hai) as Hlow.
    assert (NF : ~ (F <= a < F + 128)) by (intros Hx; exact (NIMG a Hx Hai)).
    rewrite KEEP; [exact (Hrom a Ha Ho He) | dc_num | dc_num | dc_num | dc_num].
  - intros Hn0. destruct (Hbuf Hn0) as (Hra & Hhull & Hbp).
    destruct (Hbufpre Hn0) as (Hb0 & _ & (m & Hm & _ & Hnm) & _ & _ & _ & _).
    rewrite <- Hab in Hm.
    pose proof (sep_block_frame rsegs B LAWS (dx_lyc c) S1 W1 mem2 md2 _ m DC_CID pos HAR2 Hm Hin1) as Hsep.
    destruct (al_blocks _ _ LAWS (dx_lyc c) S1 W1 mem2 md2 _ m HAR2 Hm) as (_ & _ & Hbc & Hbapp & _).
    pose proof (req_size_pos m ltac:(lia)) as Hrq.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes DC_CID) with 128 in Hsep.
    unfold in_app in Hbapp.
    split; [|split].
    + apply (rtmb_ra_kept rsegs (w_H W1) mem1 (w_H W1) mem2 SHADOW_OFF _ _ Hra).
      intros x Hx. apply KEEP; dc_num.
    + apply (rtmb_hull_kept rsegs (w_H W1) mem1 (w_H W1) mem2 _ _ Hhull).
      intros s Hs Hne. rewrite KEEP; [exact Hne | dc_num | dc_num | dc_num | dc_num].
    + intros a Ha. apply Hpr. apply Hbp. exact Ha.
  - intros a Ha Hs Ho.
    assert (NF : ~ (F <= a < F + 128)).
    { intros Hx. apply Ho. apply (YF0v.own_free_frame B (dx_lyc c) (dx_Sc c) _ DC_CID pos a (proj1 (proj1 HJc)));
        [unfold DC_CID; lia | exact Hpos | exact Hnin | exact Hx]. }
    rewrite KEEP; [exact (Hkept a Ha Hs Ho) | exact Ha | lia | lia | unfold T_dcsv_STK in Hs; unfold ESTACK in *; lia].
Qed.
End carry.

(* ======================================== the blocks' small facts ======================================== *)
Section den2. Context {fx : YK11.FPState}.
Lemma dc_den_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (Ereg regs extra) (SOff n 0) = getr regs r.
Proof.
  intros regs extra n r Hn. apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regs extra n r Hn), Z.add_0_r.
  apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
  unfold M64. lia.
Qed.
End den2.
(* every byte outside Wr is kept by a run whose write windows lie in Wr *)
Lemma dc_kept_wr : forall E (rs : smem) (H : word -> bool) (m m' : word -> option byte) (Wr : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> Wr a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
  intros E rs H m m' Wr HF HW a Ha Hn. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by exact Ha. intros X. exact (Hn (HW a X)).
Qed.
(* the shadow byte of a frame the walk owns is a byte it may write *)
Lemma dc_awr_fsh : forall STK sp0 FP bl0 blc ly own pos a,
  In (DC_CID, pos) own -> shadow_addr (frame_addr ly DC_CID pos) <= a < shadow_addr (frame_addr ly DC_CID pos) + 16 ->
  awr_byte STK sp0 FP bl0 blc ly own a.
Proof.
  intros STK sp0 FP bl0 blc ly own pos a Hown Ha. right; right; right. exists DC_CID, pos. split; [exact Hown|]. right.
  unfold in_zr; cbn [fst snd]. change (fs_frame_bytes DC_CID / 8) with 16. lia.
Qed.
(* a byte of the frame the walk owns is a byte it may write *)
Lemma dc_awr_fobj : forall STK sp0 FP bl0 blc ly own pos a,
  In (DC_CID, pos) own -> frame_addr ly DC_CID pos <= a < frame_addr ly DC_CID pos + 128 ->
  awr_byte STK sp0 FP bl0 blc ly own a.
Proof.
  intros STK sp0 FP bl0 blc ly own pos a Hown Ha. right; right; right. exists DC_CID, pos. split; [exact Hown|]. left.
  unfold in_zr; cbn [fst snd]. change (fs_frame_bytes DC_CID) with 128. lia.
Qed.

(* ======================================== block C1: the bit set, to the snprintf call ======================================== *)
(* 0x844c4 `beqz a0` not taken (a0 = the bit); 0x844c8 s4 := a3 (~tmp, the operand of the two trap tests);
   0x844cc / 0x844d0 the two shadow bytes of cell := 0 (s2 = the frame's shadow address);
   0x844d4 a3 := "" (R+64); 0x844d8 `beqz s5`: len = 0 keeps "", else 0x844dc a3 := "," (R+40);
   0x844e0 .. 0x844e8 a1 := 16, a0 := cell (R+72, env slot 32), a2 := "%s%d" (s9); 0x844ec `jal 0x4222c`,
   ra = 0x844f0 *)
Definition dcC1_frame : YP09.region :=
  YP09.mkRegion (Some 9%nat) 40 80 0 0
   [YP09.mkChunk 40 (CVal 8 (SLit SNP_COMMA)); YP09.mkChunk 64 (CVal 8 (SLit SNP_EMPTY)); YP09.mkChunk 72 (CVal 8 (SOff 32 0))].
Definition dcC1_sh : YP09.region := YP09.mkRegion (Some 18%nat) 12 14 12 14 [].
(* z: len = 0 (s5 the literal 0) or len in [1, 17] (s5 its atom) *)
Definition dcC1_pins (i : nat) (z : bool) : list (bv 5 * sv) :=
  if z then [((10%bv : bv 5), SLit (dc_bit i)); ((21%bv : bv 5), SLit 0)] else [((10%bv : bv 5), SLit (dc_bit i))].
Definition dcC1_regs (i : nat) (z : bool) : list sv :=
  if z then sr_set (sr_set sr_atoms (10%bv : bv 5) (SLit (dc_bit i))) (21%bv : bv 5) (SLit 0)
  else sr_set sr_atoms (10%bv : bv 5) (SLit (dc_bit i)).
Definition dcC1_facts (z : bool) : facts := if z then mkFacts [] [] [] else mkFacts [(21%nat, mkAF 1 17 0)] [] [].
Definition dcC1_ss (i : nat) (z : bool) : sstate := mkSS 0x844c4 (dcC1_regs i z) [dcC1_frame; dcC1_sh] None (dcC1_facts z).
Definition dc_len_ok (z : bool) (len : Z) : Prop := if z then len = 0 else 1 <= len <= 17.

Definition dcC1_R (z : bool) (regsA : bvmap 5 word) (W : world rsegs) (shF F : Z) (i : nat) :
  bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 mem2 => getr regs2 1 = w64 DC_RA_SNP /\ getr regs2 10 = w64 (F + 96) /\ getr regs2 11 = w64 SNP_SIZE /\
    getr regs2 12 = getr regsA 25 /\ getr regs2 13 = w64 (if z then SNP_EMPTY else SNP_COMMA) /\
    getr regs2 20 = getr regsA 13 /\
    aview rsegs (w_H W) mem2 (shF + 12) = Some 0 /\ aview rsegs (w_H W) mem2 (shF + 13) = Some 0.

Section blkC1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma dcC1_entry : forall (W : world rsegs) regs mem (i : nat) (z : bool) R F shF len,
  getr regs 9 = w64 R -> getr regs 10 = w64 (dc_bit i) -> getr regs 18 = w64 shF -> getr regs 21 = w64 len ->
  dc_len_ok z len ->
  2 ^ 46 <= R -> R + 224 <= 2 ^ 47 -> 4096 <= F -> F + 128 <= 2 ^ 47 -> 0 <= shF -> shF + 16 <= 2 ^ 46 ->
  val_mem rsegs (mrestrict (w_H W) mem) (R + 40) 8 SNP_COMMA ->
  val_mem rsegs (mrestrict (w_H W) mem) (R + 64) 8 SNP_EMPTY ->
  val_mem rsegs (mrestrict (w_H W) mem) (R + 72) 8 (F + 96) ->
  (forall a, shF <= a < shF + 16 -> apresent (w_H W) mem a) ->
  st_ok rsegs (Ereg regs [w64 (F + 96)]) (dcC1_ss i z)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 0x844c4) mem (seg_rom rsegs))).
Proof.
  intros W regs mem i z R F shF len H9 H10 H18 H21 Hz HR0 HR1 HF0 HF1 Hs0 Hs1 V40 V64 V72 Hp.
  rewrite restrict_mkst_fx.
  assert (E9 : bv_unsigned (ew (Ereg regs [w64 (F + 96)]) 9) = R)
    by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (E18 : bv_unsigned (ew (Ereg regs [w64 (F + 96)]) 18) = shF)
    by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18; apply unsigned_lit_small; lia).
  assert (E32 : ew (Ereg regs [w64 (F + 96)]) 32 = Z_to_bv 64 (F + 96)) by exact (ew_Ereg_extra regs _ 0).
  assert (HS0 : st_ok rsegs (Ereg regs [w64 (F + 96)]) (mkSS 0x844c4 sr_atoms [dcC1_frame; dcC1_sh] None (dcC1_facts z))
    (mkst regs (Z_to_bv 64 0x844c4) (mrestrict (w_H W) mem) (seg_rom rsegs))).
  { apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (rtmb_ro_region rsegs _ _ _ 9 R); [exact E9 | lia | lia |].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        * apply (chunk_ok_val rsegs _ _ R 40 8 (SLit SNP_COMMA) SNP_COMMA);
            [reflexivity | cbn; unfold SNP_COMMA; lia | lia | exact V40].
        * apply (chunk_ok_val rsegs _ _ R 64 8 (SLit SNP_EMPTY) SNP_EMPTY);
            [reflexivity | cbn; unfold SNP_EMPTY; lia | lia | exact V64].
        * apply (chunk_ok_val rsegs _ _ R 72 8 (SOff 32 0) (F + 96)); [| cbn; lia | lia | exact V72].
          apply bv_eq. rewrite denot_SOff, E32, Z.add_0_r, unsigned_lit_small by lia.
          apply zcanon_id. unfold M64. lia.
      + apply (rtmb_rw_region rsegs _ _ _ 18 shF); [exact E18 | lia | lia | | apply Forall_nil].
        intros o Ho. apply Hp. lia.
    - apply pairwise_disjoint_of_extents. unfold dcC1_frame, dcC1_sh, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E18.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - destruct z; (split; [|split; [exact I | exact I]]); cbn [dcC1_facts f_atoms atoms_ok]; [exact I|].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. cbn [dc_len_ok] in Hz.
      rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl), H21, unsigned_lit_small by lia.
      rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) _ HS0 eq_refl H10) as HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
  destruct z.
  - cbn [dc_len_ok] in Hz. subst len.
    pose proof (st_ok_pin_lit rsegs _ _ _ (21%bv : bv 5) 0 HS1 eq_refl H21) as HS2.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. exact HS2.
  - exact HS1.
Qed.
End blkC1.

Ltac dcC1_run HS HJ E18 E32 regs extra Hown :=
  aj_run_to dc_tbl_ok HS HJ SNP_TRAMP;
  [ (* the write window: the two shadow bytes of cell *)
    cbn [ss_mem dcC1_ss]; apply awr_ok_cons_ro; [cbn; lia|];
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat); [reflexivity | exact E18 | | apply awr_ok_nil];
    let a := fresh "a" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi dcC1_sh] in Ha; apply (dc_awr_fsh _ _ _ _ _ _ _ _ _ Hown); lia
  | lazymatch goal with |- context [dcC1_R ?z _ _ _ _ ?j] =>
    dcb_leaf regs extra (dcC1_pins j z) dc_pins_lit
      ltac:(let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn;
            lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
            lazymatch type of Hn with ~ ?P => let f := eval pattern a in P in lazymatch f with ?g _ =>
              apply (dc_kept_wr _ _ _ _ _ g HFr); [| exact Ha | exact Hn] end end end;
            let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
            intros x (r & Hin & Hr); cbn [ss_mem dcC1_ss In] in Hin;
            destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val dcC1_frame dcC1_sh] in Hr;
            [lia | rewrite E18 in Hr; lia])
      ltac:(fun HSf =>
        let Hr1 := fresh "Hr1" in
        assert (Hr1 : region_ok rsegs (Ereg regs extra) (mrestrict (w_H _) (ms_mem _))
          (YP09.mkRegion (Some 18%nat) 12 14 12 14 [YP09.mkChunk 13 (CVal 1 (SLit 0)); YP09.mkChunk 12 (CVal 1 (SLit 0))]))
          by exact (rtsb_region_nth _ _ _ 1 _ _ HSf eq_refl);
        split; [dc_sv HSf; reflexivity|];
        split; [dc_sv HSf; apply dc_den_atom; [dc_ew; exact E32 | lia]|];
        split; [dc_sv HSf; reflexivity|];
        split; [dc_sv HSf; apply dc_den_reg; reflexivity|];
        split; [dc_sv HSf; reflexivity|];
        split; [dc_sv HSf; apply dc_den_reg; reflexivity|];
        split; [apply (rtsb_chunk0 (Ereg regs extra)); apply (rtsb_chunks _ _ _ _ _ _ _ _ _ Hr1 E18); right; left; reflexivity|];
        apply (rtsb_chunk0 (Ereg regs extra)); apply (rtsb_chunks _ _ _ _ _ _ _ _ _ Hr1 E18); left; reflexivity)
    end ].

Section blkC1b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Lemma dcb_C1 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md (i : nat) (z : bool) R len pos,
  (i < 3)%nat ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem md k ->
  In (DC_CID, pos) own ->
  getr regs 9 = w64 R -> getr regs 10 = w64 (dc_bit i) ->
  getr regs 18 = w64 (shadow_addr (frame_addr lyc DC_CID pos)) -> getr regs 21 = w64 len -> dc_len_ok z len ->
  2 ^ 46 <= R -> R + 224 <= 2 ^ 47 ->
  4096 <= frame_addr lyc DC_CID pos -> frame_addr lyc DC_CID pos + 128 <= 2 ^ 47 ->
  0 <= shadow_addr (frame_addr lyc DC_CID pos) ->
  shadow_addr (frame_addr lyc DC_CID pos) + 16 <= 2 ^ 46 ->
  val_mem rsegs (mrestrict (w_H W1) mem) (R + 40) 8 SNP_COMMA ->
  val_mem rsegs (mrestrict (w_H W1) mem) (R + 64) 8 SNP_EMPTY ->
  val_mem rsegs (mrestrict (w_H W1) mem) (R + 72) 8 (frame_addr lyc DC_CID pos + 96) ->
  (forall a, shadow_addr (frame_addr lyc DC_CID pos) <= a < shadow_addr (frame_addr lyc DC_CID pos) + 16 ->
     apresent (w_H W1) mem a) ->
  SRr rsegs W1 (cfg_at rsegs 0x844c4 regs mem md)
    (dcb_post B STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md SNP_TRAMP [1; 10; 11; 12; 13; 20]%bv
       (fun a => shadow_addr (frame_addr lyc DC_CID pos) + 12 <= a < shadow_addr (frame_addr lyc DC_CID pos) + 14)
       (dcC1_R z regs W1 (shadow_addr (frame_addr lyc DC_CID pos)) (frame_addr lyc DC_CID pos) i)).
Proof using LAWS.
  intros STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md i z R len pos
    Hi HJ Hown H9 H10 H18 H21 Hz HR0 HR1 HF0 HF1 Hs0 Hs1 V40 V64 V72 Hp.
  pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
  pose proof (dcC1_entry W1 regs mem i z R (frame_addr lyc DC_CID pos) (shadow_addr (frame_addr lyc DC_CID pos)) len
    H9 H10 H18 H21 Hz HR0 HR1 HF0 HF1 Hs0 Hs1 V40 V64 V72 Hp) as HS.
  assert (E18 : bv_unsigned (ew (Ereg regs [w64 (frame_addr lyc DC_CID pos + 96)]) 18) = shadow_addr (frame_addr lyc DC_CID pos))
    by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18; apply unsigned_lit_small; lia).
  assert (E32 : ew (Ereg regs [w64 (frame_addr lyc DC_CID pos + 96)]) 32 = Z_to_bv 64 (frame_addr lyc DC_CID pos + 96))
    by exact (ew_Ereg_extra regs _ 0).
  unfold cfg_at. change (w64 0x844c4) with (Z_to_bv 64 0x844c4).
  destruct z; cbn [dc_len_ok] in Hz; [subst len|];
  (destruct i as [|[|[|i]]]; [| | | lia]);
  dcC1_run HS HJ E18 E32 regs [w64 (frame_addr lyc DC_CID pos + 96)] Hown.
Qed.
End blkC1b.

(* ======================================== the snprintf call ======================================== *)
(* rate_snprintf_sd_realizes at the call, carried under the caller's journal (as RtPgStepsB.v rtsb_ecall_at, with the
   float state the wrapper returns at, related to the caller's by rt_fxk [10]) *)
Section snp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Definition dc_snp_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (lyc : alayout) (S1 : astate)
  (W1 : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d v : Z) (sep : list Z)
  : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W1 /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
  c2 = @cfg_at fx' rsegs DC_RA_SNP regs2 mem2 md2 /\ rt_fxk [10] fx fx' /\
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem2 md2 k /\
  aregs_preserved regs regs2 /\ same_io md md2 /\
  getr regs2 10 = w64 (Z.of_nat (length (snp_text sep v))) /\
  (forall i, 0 <= i < Z.of_nat (length (snp_dest_bytes (snp_text sep v))) ->
     aview rsegs (w_H W1) mem2 (d + i) = Some (nth (Z.to_nat i) (snp_dest_bytes (snp_text sep v)) 0)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + SNP_SIZE) -> ~ (spZ regs - SNP_STK <= a < spZ regs) ->
     aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W1) mem a) /\
  (forall a, apresent (w_H W1) mem a -> apresent (w_H W1) mem2 a).
Lemma dc_snp_call : forall STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md (o d x v : Z) (sep : list Z),
  @rate_snprintf_sd_realizes fx rc rsegs B SNP_TRAMP ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> SNP_STK - o <= STK ->
  getr regs 1 = w64 DC_RA_SNP -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 SNP_SIZE -> getr regs 12 = w64 SNP_FMT -> getr regs 13 = w64 x ->
  (x = SNP_EMPTY /\ sep = [] \/ x = SNP_COMMA /\ sep = [44]) ->
  -2 ^ 31 <= v < 2 ^ 31 -> bv_unsigned (getr regs 14) mod 2 ^ 32 = v mod 2 ^ 32 ->
  snp_cstr rsegs (w_H W1) mem SNP_FMT SNP_FMT_BYTES -> snp_cstr rsegs (w_H W1) mem x sep ->
  snp_rom_kept rsegs B W1 mem ->
  0 < d -> d + SNP_SIZE + 8 <= 2 ^ 63 ->
  dest_ok rsegs B lyc S1 W1 regs mem d SNP_SIZE ->
  (forall a, d <= a < d + SNP_SIZE -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S1) lyc own a) ->
  amem_range d (SNP_SIZE + 8) ->
  range_addressable (aview rsegs (w_H W1) mem) SHADOW_OFF d SNP_SIZE ->
  shadow_hull_vis (aview rsegs (w_H W1) mem) d SNP_SIZE ->
  (d + SNP_SIZE <= spZ regs - SNP_STK \/ spZ regs <= d) ->
  (d + SNP_SIZE <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= d) ->
  YK0o.frm_zero (@fp_csr fx) ->
  SRr rsegs W1 (cfg_at rsegs SNP_TRAMP regs mem md)
    (dc_snp_post STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md d v sep).
Proof using LAWS.
  intros STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md o d x v sep
    RS HJ Hsp Hal Hneg Hbud Hra Hgp Htp H10 H11 H12 H13 Hsep Hv H14 Cf Cx Hrom Hd0 Hd1 Hdest Hdw Hamr Hra_d Hhull
    Hwin Himg Hfrm.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
  assert (Hes : ESTACK = 4096) by reflexivity. unfold SNP_STK in *.
  assert (HPRE : ecall_pre rsegs B lyc S1 W1 regs mem md).
  { eapply (ecall_pre_at rsegs B) with (o := o); try eassumption; [lia | rewrite Hra; reflexivity]. }
  destruct (rtsb_stk_window B STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem md k regs o (2 * ESTACK) HJ Hsp Hneg ltac:(lia))
    as (Hlo & Hpw).
  eapply SRr_mono.
  { exact (RS lyc S1 W1 regs mem md d x v sep HPRE Hlo Hpw H10 H11 H12 H13 Hsep Hv H14 Cf Cx Hrom Hd0 Hd1 Hdest Hamr
      Hra_d Hhull Hwin Himg Hfrm). }
  cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & -> & Hreg & Hfrm' & HAR2 & HP & Hsame & H10' & Hbytes & Hkeep & Hpres2).
  assert (Hlen : (length (snp_dest_bytes (snp_text sep v)) <= 16)%nat).
  { unfold snp_dest_bytes, SNP_SIZE. rewrite length_app, length_firstn. cbn [length]. lia. }
  split; [reflexivity|]. exists fx', regs2, mem2, md2.
  split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [split; [intros kk Hkk; apply Hreg; intros E; apply Hkk; left; symmetry; exact E | exact Hfrm']|].
  split.
  { eapply (ajournal_after_write rsegs B LAWS rtsb_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem md k mem2 md2
      (fun a => (d <= a < d + SNP_SIZE) \/ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) S1 own HJ).
    - intros a Ha Hna. apply (Hkeep a Ha).
      + intros H'. apply Hna. left. unfold SNP_SIZE in *. lia.
      + intros H'. apply Hna. right. rewrite Hsp in H'. exact H'.
    - exact Hpres2.
    - exact Hsame.
    - intros a [Ha | Ha]; left; [exact (Hdw a Ha) | left; lia].
    - exact HAR2.
    - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
  split; [exact HP|]. split; [apply same_io_materialized; exact Hsame|]. split; [exact H10'|].
  split; [exact Hbytes|].
  split; [|exact Hpres2].
  intros a Ha Hn1 Hn2. apply (Hkeep a Ha); [|exact Hn2]. intros H'. apply Hn1. unfold SNP_SIZE in *. lia.
Qed.
End snp.

(* ======================================== the __asan_memcpy call ======================================== *)
(* RtPgStepsB.v rtsb_intrin_at for OCpy, also keeping presence (for the next cut state's frame facts) *)
Section cpy. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Definition dc_cpy_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (lyc : alayout) (S1 : astate)
  (W1 : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (retpc d x n : Z)
  : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W1 /\ exists regs2 mem2 md2,
  c2 = cfg_at rsegs retpc regs2 mem2 md2 /\
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem2 md2 k /\
  aregs_preserved regs regs2 /\ same_io md md2 /\ getr regs2 10 = w64 d /\
  (forall i, 0 <= i < n -> aview rsegs (w_H W1) mem2 (d + i) = aview rsegs (w_H W1) mem (x + i)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
     aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W1) mem a) /\
  (forall a, apresent (w_H W1) mem a -> apresent (w_H W1) mem2 a).
Lemma dc_cpy_call : forall STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md (o retpc d x n : Z),
  @aintrin_realizes fx rc rsegs B OCpy B_MEMCPY ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem md k ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regs 1 = w64 retpc -> YK0s.ret_ok (w64 retpc) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
  (forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S1) lyc own a /\
     ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
  amem_range d n -> range_addressable (aview rsegs (w_H W1) mem) SHADOW_OFF d n ->
  (0 < n -> shadow_hull_vis (aview rsegs (w_H W1) mem) d n) ->
  0 <= x -> x + n <= 2 ^ 63 -> src_ok rsegs W1 regs mem x n -> (d + n <= x \/ x + n <= d) -> amem_range x n ->
  range_addressable (aview rsegs (w_H W1) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview rsegs (w_H W1) mem) x n) ->
  SRr rsegs W1 (cfg_at rsegs B_MEMCPY regs mem md)
    (dc_cpy_post STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md retpc d x n).
Proof using LAWS.
  intros STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md o retpc d x n
    AI HJ Hsp Hal Hneg Hbud Hra Hraw Hgp Htp Ha0 Ha1 Ha2 Hn Hd0 Hdn Hdest Hamr Hra_d Hhull Hx0 Hxn Hsrc Hov Hamx Hrax Hhx.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
  assert (HPRE : ecall_pre rsegs B lyc S1 W1 regs mem md).
  { eapply (ecall_pre_at rsegs B) with (o := o); try eassumption. rewrite Hra. exact Hraw. }
  assert (HDEST : dest_ok rsegs B lyc S1 W1 regs mem d n).
  { intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
    assert (Hpa : apresent (w_H W1) mem a /\ ~ aowned B lyc S1 a) by (eapply (awr_byte_present rsegs B); eassumption).
    destruct Hpa as [Hp Hno]. rewrite Hsp.
    split; [apply (apresent_writable rsegs); exact Hp | auto]. }
  eapply SRr_mono.
  { exact (AI lyc S1 W1 regs mem md d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull
      (conj Hx0 (conj Hxn (conj Hsrc (conj Hov (conj Hamx (conj Hrax Hhx))))))). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
  rewrite Hsp in Hfr.
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split.
  { eapply (ajournal_after_write rsegs B LAWS rtsb_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem md k mem2 md2
      (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) S1 own HJ).
    - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
    - exact Hpres2.
    - exact Hsame.
    - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; lia].
    - exact HAR2.
    - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
  split; [exact HP|]. split; [apply same_io_materialized; exact Hsame|]. split; [exact Hres|].
  split; [exact Heff|]. split; [|exact Hpres2].
  intros a Ha Hn1 Hn2. apply (Hfr a Ha Hn1). rewrite <- Hsp. exact Hn2.
Qed.
End cpy.

(* ======================================== block C2: after snprintf, to __asan_memcpy ======================================== *)
(* 0x844f0 `bltz a0` not taken (a0 = |T|, 5 or 6); 0x844f4 a2 := |T|; 0x844f8 s3 := len + |T|; 0x844fc a0 := 31;
   0x84500 a3 := s4 (~tmp); 0x84504 `bltu 31,s3` not taken (len + |T| <= 23);
   THE TRAP BRANCH 0x84508 `bltu a3,s5` (to the `unimp` 0x846e8: tmp + len would wrap) not taken: the engine decides
   it by itself from the atom ranges of the state, s4's atom (a3 = s4) in [2^63, 2^64 - 1] (~tmp = 2^64 - 1 - (F + 32)
   with F + 128 <= 2^47) against s5, the literal 0 (z) or its atom in [1, 17];
   0x8450c a0 := tmp (R+48, env slot 32); 0x84510 a0 := tmp + len; 0x84514 a1 := cell (R+72, slot 32 + 64);
   0x84518 `jal 0x518b8`, ra = 0x8451c *)
Definition dcC2_frame : YP09.region :=
  YP09.mkRegion (Some 9%nat) 48 80 0 0 [YP09.mkChunk 48 (CVal 8 (SOff 32 0)); YP09.mkChunk 72 (CVal 8 (SOff 32 64))].
Definition dcC2_pins (nT : Z) (z : bool) : list (bv 5 * sv) :=
  if z then [((10%bv : bv 5), SLit nT); ((21%bv : bv 5), SLit 0)] else [((10%bv : bv 5), SLit nT)].
Definition dcC2_regs (nT : Z) (z : bool) : list sv :=
  if z then sr_set (sr_set sr_atoms (10%bv : bv 5) (SLit nT)) (21%bv : bv 5) (SLit 0)
  else sr_set sr_atoms (10%bv : bv 5) (SLit nT).
(* the facts of C1 and the range of s4's atom, closed numerals (RtPgStepsB.v PART 2b): ~tmp >= 2^63 *)
Definition dcC2_facts (z : bool) : facts :=
  if z then mkFacts [(20%nat, mkAF 9223372036854775808 18446744073709551615 0)] [] []
  else mkFacts [(21%nat, mkAF 1 17 0); (20%nat, mkAF 9223372036854775808 18446744073709551615 0)] [] [].
Definition dcC2_ss (nT : Z) (z : bool) : sstate := mkSS DC_RA_SNP (dcC2_regs nT z) [dcC2_frame] None (dcC2_facts z).

Section blkC2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma dcC2_entry : forall (W : world rsegs) regs mem (z : bool) R F nT len,
  getr regs 9 = w64 R -> getr regs 10 = w64 nT -> getr regs 20 = w64 (2 ^ 64 - 1 - (F + 32)) -> getr regs 21 = w64 len ->
  dc_len_ok z len ->
  2 ^ 46 <= R -> R + 224 <= 2 ^ 47 -> 4096 <= F -> F + 128 <= 2 ^ 47 ->
  val_mem rsegs (mrestrict (w_H W) mem) (R + 48) 8 (F + 32) ->
  val_mem rsegs (mrestrict (w_H W) mem) (R + 72) 8 (F + 96) ->
  st_ok rsegs (Ereg regs [w64 (F + 32)]) (dcC2_ss nT z)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 DC_RA_SNP) mem (seg_rom rsegs))).
Proof.
  intros W regs mem z R F nT len H9 H10 H20 H21 Hz HR0 HR1 HF0 HF1 V48 V72.
  rewrite restrict_mkst_fx.
  assert (E9 : bv_unsigned (ew (Ereg regs [w64 (F + 32)]) 9) = R)
    by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (E32 : ew (Ereg regs [w64 (F + 32)]) 32 = Z_to_bv 64 (F + 32)) by exact (ew_Ereg_extra regs _ 0).
  assert (U20 : bv_unsigned (ew (Ereg regs [w64 (F + 32)]) 20) = 2 ^ 64 - 1 - (F + 32))
    by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20; apply unsigned_lit_small; lia).
  assert (HS0 : st_ok rsegs (Ereg regs [w64 (F + 32)]) (mkSS DC_RA_SNP sr_atoms [dcC2_frame] None (dcC2_facts z))
    (mkst regs (Z_to_bv 64 DC_RA_SNP) (mrestrict (w_H W) mem) (seg_rom rsegs))).
  { apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      apply (rtmb_ro_region rsegs _ _ _ 9 R); [exact E9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (chunk_ok_val rsegs _ _ R 48 8 (SOff 32 0) (F + 32)); [| cbn; lia | lia | exact V48].
        apply bv_eq. rewrite denot_SOff, E32, Z.add_0_r, unsigned_lit_small by lia.
        apply zcanon_id. unfold M64. lia.
      + apply (chunk_ok_val rsegs _ _ R 72 8 (SOff 32 64) (F + 96)); [| cbn; lia | lia | exact V72].
        apply bv_eq. rewrite denot_SOff, E32, unsigned_lit_small by lia. rewrite unsigned_lit_small by lia.
        rewrite zcanon_id by (unfold M64; lia). lia.
    - cbn. tauto.
    - destruct z; (split; [|split; [exact I | exact I]]); cbn [dcC2_facts f_atoms atoms_ok];
      unfold afact_ok; cbn [af_lo af_hi af_al2]; cbn [dc_len_ok] in Hz;
      [ rewrite U20
      | rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl), H21, unsigned_lit_small by lia; rewrite U20 ];
      rewrite ?Z.pow_0_r, ?Z.mod_1_r;
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) _ HS0 eq_refl H10) as HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
  destruct z.
  - cbn [dc_len_ok] in Hz. subst len.
    pose proof (st_ok_pin_lit rsegs _ _ _ (21%bv : bv 5) 0 HS1 eq_refl H21) as HS2.
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. exact HS2.
  - exact HS1.
Qed.
End blkC2.

Section den3. Context {fx : YK11.FPState}.
Lemma dc_den_off : forall E n c a v, ew E n = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> v = a + c -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 v.
Proof.
  intros E n c a v Hn Ha Hv Hr. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite (U_atom_off E n a c Hn Ha) by lia. lia.
Qed.
Lemma dc_den_add_off : forall E n c m a b v, ew E n = Z_to_bv 64 a -> ew E m = Z_to_bv 64 b ->
  0 <= a < 2 ^ 64 -> 0 <= a + c < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v = a + c + b -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n c) (SOff m 0)) = w64 v.
Proof.
  intros E n c m a b v Hn Hm Ha Hac Hb Hv Hr. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E n a c Hn Ha Hac), (U_atom E m b Hm Hb).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End den3.

Definition dcC2_R (F len nT : Z) (regsA : bvmap 5 word) : bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 _ => getr regs2 1 = w64 DC_RA_CPY1 /\ getr regs2 10 = w64 (F + 32 + len) /\ getr regs2 11 = w64 (F + 96) /\
    getr regs2 12 = w64 nT /\ getr regs2 13 = getr regsA 20 /\ getr regs2 19 = w64 (len + nT).

Ltac dcC2_run HS HJ regs extra E32 E21 :=
  aj_run_to dc_tbl_ok HS HJ B_MEMCPY;
  [ awr_ok_tac
  | lazymatch goal with |- context [dcC2_R _ _ ?nT _] => lazymatch goal with HFx : frame_of _ (ss_mem (dcC2_ss _ ?z)) _ _ |- _ =>
    dcb_leaf regs extra (dcC2_pins nT z) dc_pins_lit dc_mem_nowin
      ltac:(fun HSf =>
        split; [dc_sv HSf; reflexivity|];
        split; [dc_sv HSf; first [ eapply dc_den_add_off; [exact E21 | exact E32 | lia | lia | lia | lia | lia]
                                 | eapply dc_den_add_off; [exact E32 | exact E21 | lia | lia | lia | lia | lia]
                                 | eapply dc_den_off; [exact E32 | lia | lia | lia] ] |];
        split; [dc_sv HSf; eapply dc_den_off; [exact E32 | lia | lia | lia]|];
        split; [dc_sv HSf; reflexivity|];
        split; [dc_sv HSf; apply dc_den_reg; reflexivity|];
        dc_sv HSf; first [ eapply dc_den_off; [exact E21 | lia | lia | lia] | reflexivity ])
    end end ].

Section blkC2b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Lemma dcb_C2 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md (z : bool) R F nT len,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem md k ->
  getr regs 9 = w64 R -> getr regs 10 = w64 nT -> getr regs 20 = w64 (2 ^ 64 - 1 - (F + 32)) -> getr regs 21 = w64 len ->
  dc_len_ok z len -> nT = (if z then 5 else 6) ->
  2 ^ 46 <= R -> R + 224 <= 2 ^ 47 -> 4096 <= F -> F + 128 <= 2 ^ 47 ->
  val_mem rsegs (mrestrict (w_H W1) mem) (R + 48) 8 (F + 32) ->
  val_mem rsegs (mrestrict (w_H W1) mem) (R + 72) 8 (F + 96) ->
  SRr rsegs W1 (cfg_at rsegs DC_RA_SNP regs mem md)
    (dcb_post B STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md B_MEMCPY [1; 10; 11; 12; 13; 19]%bv
       (fun _ => False) (dcC2_R F len nT regs)).
Proof using LAWS.
  intros STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md z R F nT len
    HJ H9 H10 H20 H21 Hz HnT HR0 HR1 HF0 HF1 V48 V72.
  pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
  pose proof (dcC2_entry W1 regs mem z R F nT len H9 H10 H20 H21 Hz HR0 HR1 HF0 HF1 V48 V72) as HS.
  assert (E32 : ew (Ereg regs [w64 (F + 32)]) 32 = Z_to_bv 64 (F + 32)) by exact (ew_Ereg_extra regs _ 0).
  assert (E21 : ew (Ereg regs [w64 (F + 32)]) 21 = Z_to_bv 64 len)
    by (rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
  unfold cfg_at. change (w64 DC_RA_SNP) with (Z_to_bv 64 DC_RA_SNP).
  destruct z; cbn [dc_len_ok] in Hz; [subst len|]; subst nT; dcC2_run HS HJ regs [w64 (F + 32)] E32 E21.
Qed.
End blkC2b.

(* ======================================== block C3: after __asan_memcpy, to the next head ======================================== *)
(* 0x8451c a0 := tmp (R+48, env slot 33);
   THE TRAP BRANCH 0x84520 `bltu s4,s3` (to the `unimp` 0x846e8: tmp + len + |T| would wrap) not taken: the engine
   decides it by itself from the atom ranges of the state, s4's atom in [2^63, 2^64 - 1] against s3's in [0, 23];
   0x84524 a3 := s4 (~tmp, the next head's); 0x84528 a0 := tmp + (len + |T|) (atom 32 by the alias fact);
   0x8452c `sb zero,0(a0)` the NUL; 0x84530 `j 0x84544`; 0x84544 .. 0x8454c the two shadow bytes of cell := 0xf8;
   0x84550 s5 := len + |T|; then as block B *)
Definition dcC3_nul : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition dcC3_sh : YP09.region := YP09.mkRegion (Some 18%nat) 12 14 12 14 [].
Definition dcC3_frame : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 0 0 [YP09.mkChunk 48 (CVal 8 (SOff 33 0))].
Definition dcC3_pins (i : nat) : list (bv 5 * sv) :=
  [((27%bv : bv 5), SLit (3 - Z.of_nat i)); ((23%bv : bv 5), SLit (B_ORD + 4 * Z.of_nat i));
   ((26%bv : bv 5), SLit (B_ORD + 4 * Z.of_nat i))].
Definition dcC3_regs (i : nat) : list sv :=
  sr_set (sr_set (sr_set sr_atoms (27%bv : bv 5) (SLit (3 - Z.of_nat i)))
    (23%bv : bv 5) (SLit (B_ORD + 4 * Z.of_nat i))) (26%bv : bv 5) (SLit (B_ORD + 4 * Z.of_nat i)).
(* the ranges of s3's and s4's atoms (closed numerals), and tmp + s3 as atom 32 *)
Definition dcC3_facts : facts :=
  mkFacts [(19%nat, mkAF 0 23 0); (20%nat, mkAF 9223372036854775808 18446744073709551615 0)] []
    [(SAlu ALU_ADD (SOff 33 0) (SOff 19 0), SOff 32 0)].
Definition dcC3_ss (i : nat) : sstate := mkSS DC_RA_CPY1 (dcC3_regs i) [dcC3_nul; dcC3_sh; dcC3_frame] None dcC3_facts.
(* a one-byte chunk of the literal -8 (as the engine keeps it, 2^64 - 8): the byte 0xf8 *)
Lemma dc_chunk_f8 : forall {fx : YK11.FPState} E H mem base o,
  YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 1 (SLit 18446744073709551608))) ->
  aview rsegs H mem (base + o) = Some 248.
Proof.
  intros fx E H mem base o Hc. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
  assert (Hb3 : mbyte rsegs (mrestrict H mem) (base + o) = Some b) by (rewrite <- Hb2; f_equal; cbn; ring).
  unfold aview. rewrite Hb3. cbn [cbyte YP09.c_val] in Hb1. injection Hb1 as <-.
  first [reflexivity | (vm_compute; reflexivity)].
Qed.

Section blkC3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma dcC3_entry : forall (W : world rsegs) regs mem (i : nat) R Ftmp L shF,
  getr regs 9 = w64 R -> getr regs 18 = w64 shF -> getr regs 19 = w64 L -> getr regs 20 = w64 (2 ^ 64 - 1 - Ftmp) ->
  getr regs 27 = w64 (3 - Z.of_nat i) ->
  getr regs 23 = w64 (B_ORD + 4 * Z.of_nat i) -> getr regs 26 = w64 (B_ORD + 4 * Z.of_nat i) ->
  2 ^ 46 <= R -> R + 224 <= 2 ^ 47 ->
  0 <= Ftmp -> 0 <= L -> L <= 23 -> Ftmp + L + 1 <= R -> 0 <= shF -> shF + 16 <= R ->
  (Ftmp + L + 1 <= shF + 12 \/ shF + 14 <= Ftmp + L) ->
  val_mem rsegs (mrestrict (w_H W) mem) (R + 48) 8 Ftmp ->
  apresent (w_H W) mem (Ftmp + L) ->
  (forall a, shF + 12 <= a < shF + 14 -> apresent (w_H W) mem a) ->
  st_ok rsegs (Ereg regs [w64 (Ftmp + L); w64 Ftmp]) (dcC3_ss i)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 DC_RA_CPY1) mem (seg_rom rsegs))).
Proof.
  intros W regs mem i R Ftmp L shF H9 H18 H19 H20 H27 H23 H26 HR0 HR1 Hf0 HL0 HL1 HfR Hs0 HsR Hdis V48 Hpq Hps.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs [w64 (Ftmp + L); w64 Ftmp]).
  assert (U9 : bv_unsigned (ew E 9) = R)
    by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
  assert (E19 : ew E 19 = Z_to_bv 64 L) by (subst E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
  assert (E32 : ew E 32 = Z_to_bv 64 (Ftmp + L)) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 Ftmp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
  assert (U18 : bv_unsigned (ew E 18) = shF)
    by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18; apply unsigned_lit_small; lia).
  assert (U19 : bv_unsigned (ew E 19) = L) by (rewrite E19; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = 2 ^ 64 - 1 - Ftmp)
    by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = Ftmp + L) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (HS0 : st_ok rsegs E (mkSS DC_RA_CPY1 sr_atoms [dcC3_nul; dcC3_sh; dcC3_frame] None dcC3_facts)
    (mkst regs (Z_to_bv 64 DC_RA_CPY1) (mrestrict (w_H W) mem) (seg_rom rsegs))).
  { subst E. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      + apply (rtmb_rw_region rsegs _ _ _ 32 (Ftmp + L)); [exact U32 | lia | lia | | apply Forall_nil].
        intros o Ho. replace (Ftmp + L + o) with (Ftmp + L) by lia. exact Hpq.
      + apply (rtmb_rw_region rsegs _ _ _ 18 shF); [exact U18 | lia | lia | | apply Forall_nil].
        intros o Ho. apply Hps. lia.
      + apply (rtmb_ro_region rsegs _ _ _ 9 R); [exact U9 | lia | lia |].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs _ _ R 48 8 (SOff 33 0) Ftmp); [| cbn; lia | lia | exact V48].
        apply bv_eq. rewrite denot_SOff, E33, Z.add_0_r, unsigned_lit_small by lia.
        apply zcanon_id. unfold M64. lia.
    - apply pairwise_disjoint_of_extents. unfold dcC3_nul, dcC3_sh, dcC3_frame, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, U18, U9.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; [exact I|]].
      + cbn [dcC3_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U19, U20. rewrite !Z.pow_0_r, !Z.mod_1_r.
        repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
      + cbn [dcC3_facts f_alias].
        first [apply Forall_cons; [|apply Forall_nil]; cbn [fst snd] | split; [|exact I] | idtac].
        rewrite (dc_den_off _ 32 0 (Ftmp + L) (Ftmp + L) E32) by lia.
        apply (dc_den_add_off _ 33 0 19 Ftmp L); [exact E33 | exact E19 | lia | lia | lia | lia | lia]. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (27%bv : bv 5) _ HS0 eq_refl H27) as HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
  pose proof (st_ok_pin_lit rsegs _ _ _ (23%bv : bv 5) _ HS1 eq_refl H23) as HS2.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  pose proof (st_ok_pin_lit rsegs _ _ _ (26%bv : bv 5) _ HS2 eq_refl H26) as HS3.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
  exact HS3.
Qed.
End blkC3.

Definition dcC3_R (W : world rsegs) (i : nat) (Q shF : Z) (regsA : bvmap 5 word) :
  bvmap 5 word -> (word -> option byte) -> Prop :=
  fun regs2 mem2 => getr regs2 13 = getr regsA 20 /\ getr regs2 21 = getr regsA 19 /\
    dcB_R i regs2 mem2 /\
    aview rsegs (w_H W) mem2 Q = Some 0 /\ aview rsegs (w_H W) mem2 (shF + 12) = Some 248 /\
    aview rsegs (w_H W) mem2 (shF + 13) = Some 248.

Ltac dcC3_run HS HJ regs extra U32 U18 :=
  lazymatch goal with |- context [dcB_stop ?j] => let st := eval vm_compute in (dcB_stop j) in
  aj_run_to dc_tbl_ok HS HJ st;
  [ cbn [ss_mem dcC3_ss];
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat); [reflexivity | exact U32 | |];
    [ let a := fresh "a" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi dcC3_nul] in Ha;
      match goal with Hq : forall a, _ -> awr_byte _ _ _ _ _ _ _ a |- _ => apply Hq; lia end
    | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat); [reflexivity | exact U18 | |];
      [ let a := fresh "a" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi dcC3_sh] in Ha;
        match goal with Hs : forall a, _ -> awr_byte _ _ _ _ _ _ _ a |- _ => apply Hs; lia end
      | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] ] ]
  | dcb_leaf regs extra (dcC3_pins j) dc_pins_lit
      ltac:(let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn;
            lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
            lazymatch type of Hn with ~ ?P => let f := eval pattern a in P in lazymatch f with ?g _ =>
              apply (dc_kept_wr _ _ _ _ _ g HFr); [| exact Ha | exact Hn] end end end;
            let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
            intros x (r & Hin & Hr); cbn [ss_mem dcC3_ss In] in Hin;
            destruct Hin as [<-|[<-|[<-|[]]]];
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val dcC3_nul dcC3_sh dcC3_frame] in Hr;
            [rewrite U32 in Hr; left; lia | rewrite U18 in Hr; right; lia | lia])
      ltac:(fun HSf =>
        let Hr0 := fresh "Hr0" in let Hr1 := fresh "Hr1" in
        assert (Hr0 : region_ok rsegs (Ereg regs extra) (mrestrict (w_H _) (ms_mem _))
          (YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]))
          by exact (rtsb_region_nth _ _ _ 0 _ _ HSf eq_refl);
        assert (Hr1 : region_ok rsegs (Ereg regs extra) (mrestrict (w_H _) (ms_mem _))
          (YP09.mkRegion (Some 18%nat) 12 14 12 14
            [YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551608))]))
          by exact (rtsb_region_nth _ _ _ 1 _ _ HSf eq_refl);
        split; [dc_sv HSf; apply dc_den_reg; reflexivity|];
        split; [dc_sv HSf; apply dc_den_reg; reflexivity|];
        split; [split; [dc_sv HSf; reflexivity|]; split; [dc_sv HSf; reflexivity|]; dc_sv HSf; reflexivity|];
        split; [rewrite <- (Z.add_0_r (_ : Z)) at 1; apply (rtsb_chunk0 (Ereg regs extra));
                apply (rtsb_chunks _ _ _ _ _ _ _ _ _ Hr0 U32); left; reflexivity|];
        split; [apply (dc_chunk_f8 (Ereg regs extra)); apply (rtsb_chunks _ _ _ _ _ _ _ _ _ Hr1 U18); right; left; reflexivity|];
        apply (dc_chunk_f8 (Ereg regs extra)); apply (rtsb_chunks _ _ _ _ _ _ _ _ _ Hr1 U18); left; reflexivity) ]
  end.

Section blkC3b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Lemma dcb_C3 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md (i : nat) R Ftmp L shF,
  (i < 3)%nat ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc S1 W1 mem md k ->
  getr regs 9 = w64 R -> getr regs 18 = w64 shF -> getr regs 19 = w64 L -> getr regs 20 = w64 (2 ^ 64 - 1 - Ftmp) ->
  getr regs 27 = w64 (3 - Z.of_nat i) ->
  getr regs 23 = w64 (B_ORD + 4 * Z.of_nat i) -> getr regs 26 = w64 (B_ORD + 4 * Z.of_nat i) ->
  2 ^ 46 <= R -> R + 224 <= 2 ^ 47 ->
  0 <= Ftmp -> 0 <= L -> L <= 23 -> Ftmp + L + 1 <= R -> 0 <= shF -> shF + 16 <= R ->
  (Ftmp + L + 1 <= shF + 12 \/ shF + 14 <= Ftmp + L) ->
  val_mem rsegs (mrestrict (w_H W1) mem) (R + 48) 8 Ftmp ->
  apresent (w_H W1) mem (Ftmp + L) ->
  (forall a, shF + 12 <= a < shF + 14 -> apresent (w_H W1) mem a) ->
  (forall a, Ftmp + L <= a < Ftmp + L + 1 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S1) lyc own a) ->
  (forall a, shF + 12 <= a < shF + 14 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S1) lyc own a) ->
  SRr rsegs W1 (cfg_at rsegs DC_RA_CPY1 regs mem md)
    (dcb_post B STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md (dcB_stop i) [10; 13; 21; 23; 26; 27]%bv
       (fun a => a = Ftmp + L \/ shF + 12 <= a < shF + 14) (dcC3_R W1 i (Ftmp + L) shF regs)).
Proof using LAWS.
  intros STK sp0 FP ly S W0 mem0 md0 own k lyc S1 W1 regs mem md i R Ftmp L shF Hi HJ H9 H18 H19 H20 H27 H23 H26
    HR0 HR1 Hf0 HL0 HL1 HfR Hs0 HsR Hdis V48 Hpq Hps Hwq Hws.
  pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
  pose proof (dcC3_entry W1 regs mem i R Ftmp L shF H9 H18 H19 H20 H27 H23 H26 HR0 HR1 Hf0 HL0 HL1 HfR Hs0 HsR Hdis
    V48 Hpq Hps) as HS.
  assert (U18 : bv_unsigned (ew (Ereg regs [w64 (Ftmp + L); w64 Ftmp]) 18) = shF)
    by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew (Ereg regs [w64 (Ftmp + L); w64 Ftmp]) 32) = Ftmp + L)
    by (rewrite (ew_Ereg_extra regs _ 0); apply unsigned_lit_small; lia).
  unfold cfg_at. change (w64 DC_RA_CPY1) with (Z_to_bv 64 DC_RA_CPY1).
  destruct i as [|[|[|i]]]; [| | | lia]; dcC3_run HS HJ regs [w64 (Ftmp + L); w64 Ftmp] U32 U18.
Qed.
End blkC3b.

(* ======================================== the pass's small facts ======================================== *)
Lemma dc_keep_reg : forall (regs regs' : bvmap 5 word) (clob : list (bv 5)) (r : bv 5),
  (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs' r = getr regs r) ->
  (bv_unsigned r =? 0) = false -> existsb (fun c => bv_eqb c r) clob = false -> getr regs' r = getr regs r.
Proof.
  intros regs regs' clob r Hk H0 Hc. apply Hk; [apply Z.eqb_neq; exact H0|].
  intros Hin. assert (Ht : existsb (fun c => bv_eqb c r) clob = true).
  { apply existsb_exists. exists r. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  congruence.
Qed.
(* a register a block keeps *)
Ltac dc_kr Hk := apply (dc_keep_reg _ _ _ _ Hk); reflexivity.
Lemma dc_land_clear : forall mask i, (i < 3)%nat -> Z.testbit mask (Z.of_nat i) = false -> Z.land (dc_bit i) mask = 0.
Proof.
  intros mask i Hi Hb. pose proof (RateCsv.csv_bit mask i Hi) as H. rewrite Hb in H. cbn [negb] in H.
  apply Z.eqb_eq in H. exact H.
Qed.
Lemma dc_land_set : forall mask i, (i < 3)%nat -> Z.testbit mask (Z.of_nat i) = true -> Z.land (dc_bit i) mask = dc_bit i.
Proof.
  intros mask i Hi Hb.
  assert (Hp : dc_bit i = 2 ^ Z.of_nat i) by (destruct i as [|[|[|i]]]; [| | |lia]; reflexivity).
  rewrite Hp. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec (Z.of_nat i) n) as [<-|Hne]; [rewrite Hb; reflexivity | reflexivity].
Qed.
Lemma dc_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) a l,
  garr8 rsegs (mrestrict H m) a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> aview rsegs H m' x = aview rsegs H m x) ->
  garr8 rsegs (mrestrict H m') a l.
Proof.
  intros H m m' a l G K j Hj. destruct (G j Hj) as [V Hr]. split; [|exact Hr].
  apply (val_mem_kept rsegs H H m m'); [|exact V]. intros k Hk. cbn in Hk. apply K. lia.
Qed.
(* tmp after a set pass: the prefix kept, the pass's text after it, the NUL after that *)
Lemma dc_garr8_set : forall (H : word -> bool) (m m' : word -> option byte) a (P T : list Z),
  garr8 rsegs (mrestrict H m) a (P ++ [0]) ->
  (forall x, a <= x < a + Z.of_nat (length P) -> aview rsegs H m' x = aview rsegs H m x) ->
  (forall j, 0 <= j < Z.of_nat (length T) -> aview rsegs H m' (a + Z.of_nat (length P) + j) = Some (nth (Z.to_nat j) T 0)) ->
  aview rsegs H m' (a + Z.of_nat (length P) + Z.of_nat (length T)) = Some 0 ->
  Forall (fun c => 0 <= c < 256) T ->
  garr8 rsegs (mrestrict H m') a (P ++ T ++ [0]).
Proof.
  intros H m m' a P T G K Tb N F j Hj. rewrite !length_app in Hj. cbn [length] in Hj.
  destruct (Nat.lt_ge_cases j (length P)) as [Hp|Hp].
  - rewrite app_nth1 by exact Hp. destruct (G j ltac:(rewrite length_app; cbn [length]; lia)) as [V Hr].
    rewrite app_nth1 in V, Hr by exact Hp. split; [|exact Hr].
    apply (val_mem_kept rsegs H H m m'); [|exact V]. intros k Hk. cbn in Hk. apply K. lia.
  - rewrite app_nth2 by exact Hp.
    destruct (Nat.lt_ge_cases (j - length P) (length T)) as [Ht|Ht].
    + rewrite app_nth1 by exact Ht.
      pose proof (Tb (Z.of_nat (j - length P)) ltac:(lia)) as Hv. rewrite Nat2Z.id in Hv.
      replace (a + Z.of_nat (length P) + Z.of_nat (j - length P)) with (a + Z.of_nat j) in Hv by lia.
      exact (rtmb_aview_val1 rsegs H m' _ _ Hv).
    + rewrite app_nth2 by exact Ht. replace (j - length P - length T)%nat with 0%nat by lia. cbn [nth].
      replace (a + Z.of_nat (length P) + Z.of_nat (length T)) with (a + Z.of_nat j) in N by lia.
      exact (rtmb_aview_val1 rsegs H m' _ _ N).
Qed.
Lemma dc_aview_present : forall (H : word -> bool) mem a, apresent H mem a -> aview rsegs H mem a <> None.
Proof.
  intros H mem a [Ha [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Ha, Hb. discriminate.
Qed.
Lemma dc_img_top_seg : exists sg, In sg rsegs /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) = 0x5fa000.
Proof.
  assert (H : existsb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) =? 0x5fa000) rsegs = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in H as (sg & Hin & Hb). exists sg. split; [exact Hin | apply Z.eqb_eq; exact Hb].
Qed.

Section ffacts. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
(* the live class-1 frame: 64-aligned, above the image, below the ceiling, application memory, present and not the
   runtime's, its 16 shadow bytes present, not image bytes *)
Lemma dc_frame_facts : forall ly S W mem md pos, AR rsegs B ly S W mem md -> In (DC_CID, pos) (frames S) ->
  frame_addr ly DC_CID pos mod 64 = 0 /\ YImgTop.IMG_TOP <= frame_addr ly DC_CID pos /\
  frame_addr ly DC_CID pos + 128 <= alloc_ceiling /\ in_app (frame_addr ly DC_CID pos) 128 /\
  (forall a, frame_addr ly DC_CID pos <= a < frame_addr ly DC_CID pos + 128 -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  (forall j, 0 <= j < 16 -> apresent (w_H W) mem (shadow_addr (frame_addr ly DC_CID pos) + j)) /\
  (forall a, frame_addr ly DC_CID pos <= a < frame_addr ly DC_CID pos + 128 -> ~ in_img rsegs a).
Proof using LAWS.
  intros ly S W mem md pos HAR Hin.
  pose proof (frames_bounds rsegs B LAWS ly S W mem md DC_CID pos HAR Hin) as (HF0 & HFc & HFapp).
  change (fs_frame_bytes DC_CID) with 128 in HFc, HFapp.
  destruct (al_frames _ _ LAWS ly S W mem md DC_CID pos HAR Hin) as (_ & _ & Hb & Hsh).
  change (fs_frame_bytes DC_CID) with 128 in Hb, Hsh. change (128 / 8) with 16 in Hsh.
  destruct (YG0s.frame_facts B ly S _ DC_CID pos (proj1 HAR) Hin) as (_ & _ & _ & _ & HFal & Hoff0 & _ & Hoff64 & _).
  pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO.
  pose proof (YG0t.hull_below_F ly LO) as Hhull.
  pose proof (lo_img ly LO) as (I0 & _ & _ & I3).
  destruct dc_img_top_seg as (sg & Hsg & Hsge).
  pose proof (al_img _ _ _ _ (proj1 (proj2 HAR)) sg Hsg) as [_ Hle].
  unfold page_aligned in HFal, I3. unfold kImgLo in I0.
  repeat match goal with |- _ /\ _ => split end.
  - unfold frame_addr. lia.
  - unfold frame_addr, kFakeFramesOff, DC_CID in *. lia.
  - lia.
  - exact HFapp.
  - intros a Ha. exact (Hb a Ha).
  - intros j Hj. exact (proj1 (Hsh j Hj)).
  - intros a Ha. apply (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
      (or_intror (or_introl (ex_intro _ DC_CID (ex_intro _ pos (conj Hin Ha))))))).
Qed.
End ffacts.

Lemma dc_callee : forall regs regs', aregs_preserved regs regs' ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' HP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hr. Qed.
(* a callee-saved register the call keeps *)
Ltac dc_cs HP := rewrite (dc_callee _ _ HP);
  [| lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
       let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; unfold acallee_saved; lia end].
(* a register a block keeps *)
Ltac dc_kb Hk := rewrite (dc_keep_reg _ _ _ _ Hk) by reflexivity.
Lemma dc_ra_zero : forall (rd : reader) x n,
  (forall y, x <= y < x + n -> rd (shadow_of_addr SHADOW_OFF y) = Some 0) -> range_addressable rd SHADOW_OFF x n.
Proof. intros rd x n H y Hy. exists 0. split; [exact (H y Hy) | left; reflexivity]. Qed.
Lemma dc_T_len_z : forall mask i, (i < 3)%nat ->
  Z.of_nat (length (dc_T mask i)) = if Z.of_nat (length (RateCsv.csv_prefix mask i)) =? 0 then 5 else 6.
Proof.
  intros mask i Hi. unfold dc_T, snp_text, dc_sep. rewrite length_app.
  assert (Hd : length (RateCsv.csv_dec (nth i RateCfg.closed_list 0)) = 5%nat).
  { destruct i as [|[|[|i]]]; [| | |lia]; reflexivity. }
  rewrite Hd. destruct (RateCsv.csv_prefix mask i); cbn [length]; [reflexivity|].
  replace (Z.of_nat (S (length l)) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.
Lemma dc_sep_cases : forall P : list Z,
  (if Z.of_nat (length P) =? 0 then SNP_EMPTY else SNP_COMMA) = SNP_EMPTY /\ dc_sep P = [] \/
  (if Z.of_nat (length P) =? 0 then SNP_EMPTY else SNP_COMMA) = SNP_COMMA /\ dc_sep P = [44].
Proof.
  intros [|h t]; [left; split; reflexivity | right]. cbn [length dc_sep].
  replace (Z.of_nat (S (length t)) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). split; reflexivity.
Qed.

(* ======================================== one pass ======================================== *)
Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis RT : dc_rt B MT.

Theorem dc_body : dc_body_stmt B.
Proof using RT.
  unfold dc_body_stmt.
  intros c i fq pos S1 W1 regs1 mem1 md1 Hpre HL.
  destruct RT as (LAWS & _ & _ & _ & _ & _ & _ & _ & IMG & _ & AIR & SNPR & _).
  destruct HL as (HC & Hi3 & H13 & H22 & H24 & H25 & H23 & H26 & H27).
  pose proof HC as HC'. unfold dc_core in HC'. cbv zeta in HC'.
  destruct HC' as (Hi & Hfxk & HJ & Hfr & Hnin & Hfs & Hpos & Hab & Hnev & Hsecs & Hch & Hio & Hwle & HRm & HRr &
    G2 & G3 & G4 & G8 & G9 & G18 & G21 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V112 &
    Vsav & Hflag & Htmp & Hsh & HpF & HpS & Cfmt & Ccom & Cemp & Ctab & Hrom & Hbuf & Hkept).
  pose proof Hpre as (Hcpre & _ & Hmask & _).
  pose proof Hcpre as (HJc & _ & _ & _ & _ & _ & Hwin & Hwin2 & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & _).
  change (spZ (dx_regs c)) with (dx_S0 c) in Hwin, Hwin2.
  assert (Hin1 : In (DC_CID, pos) (frames S1)) by (rewrite Hfr; left; reflexivity).
  destruct (dc_frame_facts B LAWS (dx_lyc c) S1 W1 mem1 md1 pos HAR Hin1)
    as (HF64 & HFimg & HFc & HFapp & HFp & HSp & HFni).
  unfold in_app in HFapp.
  set (F := frame_addr (dx_lyc c) DC_CID pos) in *.
  set (R := dx_R c) in *. set (S0 := dx_S0 c) in *. set (mask := dx_mask c) in *.
  assert (HR0 : 2 ^ 46 <= R) by (unfold T_dcsv_STK, ESTACK in Hwin; lia).
  assert (HR1 : R + 224 <= 2 ^ 47) by lia.
  assert (HRw : alloc_ceiling + 2 * ESTACK <= R) by (unfold T_dcsv_STK, ESTACK in *; lia).
  assert (Hlen : 0 <= Z.of_nat (length (RateCsv.csv_prefix mask i)) <= 17) by (apply dc_len_le; lia).
  (* block A: the instrumented read of ordered[i], the compare chain, the bit of the mask *)
  eapply SRr_bind.
  { exact (@dcb_A fq rc SK B LAWS _ _ _ _ _ _ _ _ _ _ _ S1 W1 regs1 mem1 md1 i R mask
      Hi3 HJ G9 H22 H24 H23 H26 HR0 HR1 Hmask V56 V80 V88 Ctab). }
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hk2 & Hio2 & Hm2 & Hp2 & (A10 & A11 & A14)).
  destruct (Z.testbit mask (Z.of_nat i)) eqn:Hbit.
  - (* the bit set *)
    assert (A10' : getr regs2 10 = w64 (dc_bit i)) by (rewrite A10, (dc_land_set mask i Hi3 Hbit); reflexivity).
    set (len := Z.of_nat (length (RateCsv.csv_prefix mask i))) in *.
    set (z := len =? 0).
    assert (Hz : dc_len_ok z len) by (unfold z, dc_len_ok; destruct (Z.eqb_spec len 0); lia).
    set (shF := shadow_addr F) in *.
    assert (HshF : SHADOW_OFF <= shF /\ shF + 16 <= kHighMemBeg) by (unfold shF, shadow_addr in *; dc_num).
    assert (Hsh8 : shF mod 8 = 0) by (unfold shF, shadow_addr, SHADOW_OFF in *; lia).
    (* block C1: s4 := ~tmp, the two shadow bytes of cell, the separator, the snprintf call's registers *)
    eapply SRr_bind.
    { refine (@dcb_C1 fq rc SK B LAWS _ _ _ _ _ _ _ _ _ _ _ S1 W1 regs2 mem2 md2 i z R len pos Hi3 HJ2
        (or_introl eq_refl) _ A10' _ _ Hz HR0 HR1 _ _ _ _ _ _ _ _).
      - transitivity (getr regs1 9); [dc_kr Hk2 | exact G9].
      - transitivity (getr regs1 18); [dc_kr Hk2 | exact G18].
      - transitivity (getr regs1 21); [dc_kr Hk2 | exact G21].
      - fold F. lia.
      - fold F. dc_num.
      - fold F shF. dc_num.
      - fold F shF. dc_num.
      - apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 mem2); [intros kk Hkk; apply Hm2; [dc_num | tauto] | exact V40].
      - apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 mem2); [intros kk Hkk; apply Hm2; [dc_num | tauto] | exact V64].
      - apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 mem2); [intros kk Hkk; apply Hm2; [dc_num | tauto] | exact V72].
      - fold F shF. intros a Ha. apply Hp2. replace a with (shF + (a - shF)) by lia. apply HSp. lia. }
    intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hk3 & Hio3 & Hm3 & Hp3 &
      (C1ra & C1a0 & C1a1 & C1a2 & C1a3 & C1s4 & C1s12 & C1s13)).
    fold F shF in Hm3, C1a0, C1s12, C1s13.
    (* the snprintf call *)
    set (sep := dc_sep (RateCsv.csv_prefix mask i)).
    set (x := if z then SNP_EMPTY else SNP_COMMA).
    assert (Hsep : x = SNP_EMPTY /\ sep = [] \/ x = SNP_COMMA /\ sep = [44]) by exact (dc_sep_cases (RateCsv.csv_prefix mask i)).
    assert (Hm31 : forall a, 0 <= a < 2 ^ 64 -> ~ (shF + 12 <= a < shF + 14) ->
      aview rsegs (w_H W1) mem3 a = aview rsegs (w_H W1) mem1 a)
      by (intros a Ha Hn; rewrite (Hm3 a Ha Hn); exact (Hm2 a Ha ltac:(tauto))).
    (* the image's strings and table at the call, from the head's: no block before it writes an image byte *)
    destruct (dc_img_carry_from B IMG (w_H W1) mem1 (dx_lyc c) S1 W1 mem3 md3 Cfmt Ccom Cemp Ctab (proj1 HJ3)
      ltac:(intros a Hai _; pose proof (rtsb_segs_low a Hai); apply Hm31; dc_num)) as (I1 & I2 & I3 & I4).
    assert (Cx : snp_cstr rsegs (w_H W1) mem3 x sep) by (destruct Hsep as [[-> ->]|[-> ->]]; [exact I3 | exact I2]).
    assert (K2_3 : getr regs3 2 = w64 R) by (dc_kb Hk3; dc_kb Hk2; exact G2).
    assert (Hsp3 : spZ regs3 = dx_sp0 c + (R - dx_sp0 c))
      by (unfold spZ; rewrite K2_3; unfold w64; rewrite unsigned_lit_small by lia; lia).
    assert (Hsp3' : spZ regs3 = R) by lia.
    eapply SRr_bind.
    { refine (@dc_snp_call fq rc SK B LAWS _ _ _ _ _ _ _ _ _ _ _ S1 W1 regs3 mem3 md3 (R - dx_sp0 c) (F + 96) x (dc_v i) sep
        (SNPR fq) HJ3 Hsp3 _ _ _ C1ra _ _ C1a0 C1a1 _ _ Hsep _ _ I1 Cx _ _ _ _ _ _ _ _ _ _ (proj2 Hfxk)).
      - lia.
      - lia.
      - unfold SNP_STK, T_dcsv_STK, ESTACK in *. lia.
      - dc_kb Hk3. dc_kb Hk2. exact G3.
      - dc_kb Hk3. dc_kb Hk2. exact G4.
      - rewrite C1a2. dc_kb Hk2. exact H25.
      - exact C1a3.
      - pose proof (dc_v_range i Hi3). lia.
      - dc_kb Hk3. rewrite A14. unfold w64. rewrite unsigned_lit_small by (pose proof (dc_v_range i Hi3); lia). reflexivity.
      - intros a Ha Ho He. assert (Hai : in_img rsegs a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
        pose proof (rtsb_segs_low a Hai) as Hlow. rewrite (Hm31 a) by dc_num. exact (Hrom a Ha Ho He).
      - lia.
      - unfold SNP_SIZE. dc_num.
      - intros a Ha. unfold SNP_SIZE in Ha. split; [|split].
        + apply (apresent_writable rsegs). apply Hp3. apply Hp2. apply HFp. lia.
        + apply HFp. lia.
        + rewrite Hsp3'. dc_num.
      - intros a Ha. unfold SNP_SIZE in Ha. eapply dc_awr_fobj; [apply in_eq | fold F; lia].
      - unfold amem_range, SNP_SIZE. dc_num.
      - apply dc_ra_zero. intros y Hy. unfold SNP_SIZE in Hy.
        assert (Hy' : shadow_of_addr SHADOW_OFF y = shF + 12 \/ shadow_of_addr SHADOW_OFF y = shF + 13)
          by (unfold shF, shadow_addr, shadow_of_addr in *; dc_num).
        destruct Hy' as [-> | ->]; assumption.
      - intros sa Hsa. unfold SNP_SIZE in Hsa.
        assert (Hs' : shF + 8 <= sa < shF + 16) by (unfold shF, shadow_addr in *; dc_num).
        apply dc_aview_present. apply Hp3. apply Hp2. replace sa with (shF + (sa - shF)) by lia. apply HSp. lia.
      - left. rewrite Hsp3'. unfold SNP_SIZE, SNP_STK. dc_num.
      - right. lia. }
    intros W4 c4 _ (-> & fx' & regs4 & mem4 & md4 & -> & Hfx4 & HJ4 & HP4 & Hio4 & S10 & Sbytes & Skeep & Spres).
    rewrite Hsp3' in Skeep.
    set (nT := Z.of_nat (length (dc_T mask i))) in *.
    assert (HnT : nT = if z then 5 else 6) by exact (dc_T_len_z mask i Hi3).
    assert (HnT' : 5 <= nT <= 6) by (rewrite HnT; destruct z; lia).
    change (snp_text sep (dc_v i)) with (dc_T mask i) in S10, Sbytes. fold nT in S10.
    assert (Hm41 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 96 <= a < F + 112) -> ~ (R - 2 * ESTACK <= a < R) ->
      ~ (shF + 12 <= a < shF + 14) -> aview rsegs (w_H W1) mem4 a = aview rsegs (w_H W1) mem1 a).
    { intros a Ha H1 H2 H3. rewrite (Skeep a Ha) by (unfold SNP_SIZE, SNP_STK in *; lia). exact (Hm31 a Ha H3). }
    (* block C2: the compare of 31 with len + |T|, THE TRAP BRANCH 0x84508, the __asan_memcpy call's registers *)
    assert (K20_4 : getr regs4 20 = w64 (2 ^ 64 - 1 - (F + 32))) by (dc_cs HP4; rewrite C1s4; dc_kb Hk2; exact H13).
    eapply SRr_bind.
    { refine (@dcb_C2 fx' rc SK B LAWS _ _ _ _ _ _ _ _ _ _ _ S1 W1 regs4 mem4 md4 z R F nT len HJ4 _ _ K20_4 _ Hz HnT
        HR0 HR1 _ _ _ _).
      - dc_cs HP4. dc_kb Hk3. dc_kb Hk2. exact G9.
      - exact S10.
      - dc_cs HP4. dc_kb Hk3. dc_kb Hk2. exact G21.
      - lia.
      - dc_num.
      - apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 mem4); [intros kk Hkk; apply Hm41; cbn in Hkk; dc_num | exact V48].
      - apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 mem4); [intros kk Hkk; apply Hm41; cbn in Hkk; dc_num | exact V72]. }
    intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & Hk5 & Hio5 & Hm5 & Hp5 &
      (C2ra & C2a0 & C2a1 & C2a2 & C2a3 & C2s3)).
    assert (Hm51 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 96 <= a < F + 112) -> ~ (R - 2 * ESTACK <= a < R) ->
      ~ (shF + 12 <= a < shF + 14) -> aview rsegs (w_H W1) mem5 a = aview rsegs (w_H W1) mem1 a).
    { intros a Ha H1 H2 H3. rewrite (Hm5 a Ha ltac:(tauto)). exact (Hm41 a Ha H1 H2 H3). }
    assert (K2_5 : getr regs5 2 = w64 R) by (dc_kb Hk5; dc_cs HP4; exact K2_3).
    assert (Hsp5 : spZ regs5 = dx_sp0 c + (R - dx_sp0 c))
      by (unfold spZ; rewrite K2_5; unfold w64; rewrite unsigned_lit_small by lia; lia).
    assert (Hsp5' : spZ regs5 = R) by lia.
    (* the shadow bytes of tmp's first three granules are 0, of cell's first 0 *)
    assert (Sh0 : forall j, 4 <= j < 7 -> aview rsegs (w_H W1) mem5 (shF + j) = Some 0).
    { intros j Hj. rewrite (Hm51 (shF + j)) by dc_num. unfold shF. rewrite (Hsh j ltac:(cbn; lia)).
      destruct (Z.eq_dec j 4) as [->|]; [reflexivity|]. destruct (Z.eq_dec j 5) as [->|]; [reflexivity|].
      replace j with 6 by lia. reflexivity. }
    assert (Sh12 : aview rsegs (w_H W1) mem5 (shF + 12) = Some 0).
    { rewrite (Hm5 (shF + 12) ltac:(dc_num) ltac:(tauto)).
      rewrite (Skeep (shF + 12) ltac:(dc_num)) by (unfold SNP_SIZE, SNP_STK; dc_num). exact C1s12. }
    (* __asan_memcpy(tmp + len, cell, |T|) *)
    eapply SRr_bind.
    { refine (@dc_cpy_call fx' rc SK B LAWS _ _ _ _ _ _ _ _ _ _ _ S1 W1 regs5 mem5 md5 (R - dx_sp0 c) DC_RA_CPY1
        (F + 32 + len) (F + 96) nT (AIR fx') HJ5 Hsp5 _ _ _ C2ra ltac:(vm_compute; reflexivity) _ _ C2a0 C2a1 C2a2
        _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      - lia.
      - lia.
      - unfold T_dcsv_STK, ESTACK in *. lia.
      - dc_kb Hk5. dc_cs HP4. dc_kb Hk3. dc_kb Hk2. exact G3.
      - dc_kb Hk5. dc_cs HP4. dc_kb Hk3. dc_kb Hk2. exact G4.
      - lia.
      - lia.
      - dc_num.
      - intros a Ha. split; [eapply dc_awr_fobj; [apply in_eq | fold F; lia] | unfold ESTACK in *; lia].
      - unfold amem_range. dc_num.
      - apply dc_ra_zero. intros y Hy.
        assert (Hy' : exists j, 4 <= j < 7 /\ shadow_of_addr SHADOW_OFF y = shF + j)
          by (exists ((y - F) / 8); unfold shF, shadow_addr, shadow_of_addr in *; dc_num).
        destruct Hy' as (j & Hj & ->). exact (Sh0 j Hj).
      - intros _ sa Hsa.
        assert (Hs' : shF <= sa < shF + 8) by (unfold shF, shadow_addr in *; dc_num).
        apply dc_aview_present. apply Hp5. apply Spres. apply Hp3. apply Hp2.
        replace sa with (shF + (sa - shF)) by lia. apply HSp. lia.
      - lia.
      - dc_num.
      - intros a Ha. split.
        + rewrite (Hm5 a ltac:(lia) ltac:(tauto)).
          pose proof (Sbytes (a - (F + 96)) ltac:(rewrite (dc_dest_bytes mask i Hi3), length_app; cbn [length]; fold nT; lia))
            as Hb. replace (F + 96 + (a - (F + 96))) with a in Hb by lia. rewrite Hb. discriminate.
        + rewrite Hsp5'. unfold ESTACK in *. lia.
      - lia.
      - unfold amem_range. dc_num.
      - apply dc_ra_zero. intros y Hy.
        assert (Hy' : shadow_of_addr SHADOW_OFF y = shF + 12) by (unfold shF, shadow_addr, shadow_of_addr in *; dc_num).
        rewrite Hy'. exact Sh12.
      - intros _ sa Hsa.
        assert (Hs' : shF + 8 <= sa < shF + 16) by (unfold shF, shadow_addr in *; dc_num).
        apply dc_aview_present. apply Hp5. apply Spres. apply Hp3. apply Hp2.
        replace sa with (shF + (sa - shF)) by lia. apply HSp. lia. }
    intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hio6 & M10 & Mbytes & Mkeep & Mpres).
    rewrite Hsp5' in Mkeep.
    (* the registers block C3 reads *)
    assert (K9_6 : getr regs6 9 = w64 R) by (dc_cs HP6; dc_kb Hk5; dc_cs HP4; dc_kb Hk3; dc_kb Hk2; exact G9).
    assert (K18_6 : getr regs6 18 = w64 shF) by (dc_cs HP6; dc_kb Hk5; dc_cs HP4; dc_kb Hk3; dc_kb Hk2; exact G18).
    assert (K19_6 : getr regs6 19 = w64 (len + nT)) by (dc_cs HP6; exact C2s3).
    assert (K20_6 : getr regs6 20 = w64 (2 ^ 64 - 1 - (F + 32))) by (dc_cs HP6; dc_kb Hk5; exact K20_4).
    assert (K27_6 : getr regs6 27 = w64 (3 - Z.of_nat i)) by (dc_cs HP6; dc_kb Hk5; dc_cs HP4; dc_kb Hk3; dc_kb Hk2; exact H27).
    assert (K23_6 : getr regs6 23 = w64 (B_ORD + 4 * Z.of_nat i))
      by (dc_cs HP6; dc_kb Hk5; dc_cs HP4; dc_kb Hk3; dc_kb Hk2; exact H23).
    assert (K26_6 : getr regs6 26 = w64 (B_ORD + 4 * Z.of_nat i))
      by (dc_cs HP6; dc_kb Hk5; dc_cs HP4; dc_kb Hk3; dc_kb Hk2; exact H26).
    assert (Hpres61 : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) mem6 a)
      by (intros a Ha; apply Mpres; apply Hp5; apply Spres; apply Hp3; apply Hp2; exact Ha).
    assert (Hm61 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 + len <= a < F + 32 + len + nT) -> ~ (F + 96 <= a < F + 112) ->
      ~ (R - 2 * ESTACK <= a < R) -> ~ (shF + 12 <= a < shF + 14) -> aview rsegs (w_H W1) mem6 a = aview rsegs (w_H W1) mem1 a).
    { intros a Ha H1 H2 H3 H4. rewrite (Mkeep a Ha) by (unfold ESTACK in *; lia). exact (Hm51 a Ha H2 H3 H4). }
    (* block C3: THE TRAP BRANCH 0x84520, a3 := ~tmp, the NUL, the two shadow bytes of cell back to 0xf8,
       len := len + |T|, to the next head *)
    eapply SRr_bind.
    { refine (@dcb_C3 fx' rc SK B LAWS _ _ _ _ _ _ _ _ _ _ _ S1 W1 regs6 mem6 md6 i R (F + 32) (len + nT) shF Hi3 HJ6
        K9_6 K18_6 K19_6 K20_6 K27_6 K23_6 K26_6 HR0 HR1 _ _ _ _ _ _ _ _ _ _ _ _).
      - lia.
      - lia.
      - lia.
      - dc_num.
      - dc_num.
      - dc_num.
      - dc_num.
      - apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 mem6); [intros kk Hkk; apply Hm61; cbn in Hkk; dc_num | exact V48].
      - apply Hpres61. apply HFp. lia.
      - intros a Ha. apply Hpres61. replace a with (shF + (a - shF)) by lia. apply HSp. lia.
      - intros a Ha. eapply dc_awr_fobj; [apply in_eq | fold F; lia].
      - intros a Ha. eapply dc_awr_fsh; [apply in_eq | fold F shF; lia]. }
    intros W7 c7 _ (-> & regs7 & mem7 & md7 & -> & HJ7 & Hk7 & Hio7 & Hm7 & Hp7 &
      (C3a3 & C3s5 & (C3s11 & C3s7 & C3s10) & C3nul & C3f12 & C3f13)).
    apply SRr_ret.
    (* every byte outside tmp's new bytes, cell, the stack below R and the two shadow bytes of cell, as at the head *)
    assert (CH : forall a, 0 <= a < 2 ^ 64 -> a <> F + 32 + (len + nT) -> ~ (F + 32 + len <= a < F + 32 + len + nT) ->
      ~ (F + 96 <= a < F + 112) -> ~ (R - 2 * ESTACK <= a < R) -> ~ (shF + 12 <= a < shF + 14) ->
      aview rsegs (w_H W1) mem7 a = aview rsegs (w_H W1) mem1 a).
    { intros a Ha H1 H2 H3 H4 H5. rewrite (Hm7 a Ha) by tauto.
      rewrite (Mkeep a Ha) by (unfold ESTACK in *; lia). exact (Hm51 a Ha H3 H4 H5). }
    assert (Hst : RateCsv.csv_prefix mask (S i) = RateCsv.csv_prefix mask i ++ dc_T mask i) by exact (dc_step_set mask i Hbit).
    assert (HC7 : @dc_core fx rc SK B c (S i) pos fx' S1 W1 regs7 mem7 md7).
    { apply (@dc_carry fx rc SK B LAWS IMG c i (S i) pos fq fx' S1 W1 regs1 mem1 md1 regs7 mem7 md7 Hpre HC
        ltac:(lia) (dc_fxk_trans [10] fx fq fx' Hfxk Hfx4) HJ7).
      - eapply same_io_trans; [exact Hio2|]. eapply same_io_trans; [exact Hio3|]. eapply same_io_trans; [exact Hio4|].
        eapply same_io_trans; [exact Hio5|]. eapply same_io_trans; [exact Hio6 | exact Hio7].
      - intros a Ha Ht Hc Hw. fold F R in Ht, Hc, Hw.
        destruct (Z.eq_dec a (shF + 12)) as [->|N12].
        { rewrite C3f12. unfold shF. rewrite (Hsh 12 ltac:(cbn; lia)). reflexivity. }
        destruct (Z.eq_dec a (shF + 13)) as [->|N13].
        { rewrite C3f13. unfold shF. rewrite (Hsh 13 ltac:(cbn; lia)). reflexivity. }
        apply CH; [exact Ha | lia | lia | exact Hc | exact Hw | lia].
      - intros a Ha. apply Hp7. apply Hpres61. exact Ha.
      - dc_kb Hk7. dc_cs HP6. dc_kb Hk5. dc_cs HP4. dc_kb Hk3. dc_kb Hk2. reflexivity.
      - dc_kb Hk7. dc_cs HP6. dc_kb Hk5. dc_cs HP4. dc_kb Hk3. dc_kb Hk2. reflexivity.
      - dc_kb Hk7. dc_cs HP6. dc_kb Hk5. dc_cs HP4. dc_kb Hk3. dc_kb Hk2. reflexivity.
      - dc_kb Hk7. dc_cs HP6. dc_kb Hk5. dc_cs HP4. dc_kb Hk3. dc_kb Hk2. reflexivity.
      - dc_kb Hk7. dc_cs HP6. dc_kb Hk5. dc_cs HP4. dc_kb Hk3. dc_kb Hk2. reflexivity.
      - dc_kb Hk7. dc_cs HP6. dc_kb Hk5. dc_cs HP4. dc_kb Hk3. dc_kb Hk2. reflexivity.
      - fold mask. rewrite Hst, length_app, Nat2Z.inj_add. fold len nT. rewrite C3s5. exact K19_6.
      - fold mask F. rewrite Hst, <- app_assoc.
        apply (dc_garr8_set (w_H W1) mem1 mem7 _ _ _ Htmp).
        + intros x0 Hx0. fold len in Hx0. apply CH; dc_num.
        + intros j Hj. fold len nT in Hj |- *.
          rewrite (Hm7 (F + 32 + len + j) ltac:(dc_num)) by (unfold shF, shadow_addr in *; dc_num).
          replace (F + 32 + len + j) with (F + 32 + len + j) by reflexivity.
          rewrite (Mbytes j Hj). rewrite (Hm5 (F + 96 + j) ltac:(dc_num) ltac:(tauto)).
          rewrite (Sbytes j ltac:(rewrite (dc_dest_bytes mask i Hi3), length_app; cbn [length]; fold nT; lia)).
          rewrite (dc_dest_bytes mask i Hi3). rewrite app_nth1 by lia. reflexivity.
        + fold len nT. replace (F + 32 + len + nT) with (F + 32 + (len + nT)) by lia. exact C3nul.
        + eapply Forall_impl; [|exact (dc_T_chars mask i Hi3)]. intros cc Hcc. cbv beta in Hcc. lia. }
    assert (K13_7 : getr regs7 13 = w64 (2 ^ 64 - 1 - (F + 32))) by (rewrite C3a3; exact K20_6).
    assert (K22_7 : getr regs7 22 = w64 44100) by (dc_kb Hk7; dc_cs HP6; dc_kb Hk5; dc_cs HP4; dc_kb Hk3; dc_kb Hk2; exact H22).
    assert (K24_7 : getr regs7 24 = w64 96000) by (dc_kb Hk7; dc_cs HP6; dc_kb Hk5; dc_cs HP4; dc_kb Hk3; dc_kb Hk2; exact H24).
    assert (K25_7 : getr regs7 25 = w64 SNP_FMT) by (dc_kb Hk7; dc_cs HP6; dc_kb Hk5; dc_cs HP4; dc_kb Hk3; dc_kb Hk2; exact H25).
    destruct i as [|[|[|i]]]; [| | | lia].
    + exists fx', pos, S1, regs7, mem7, md7. split; [reflexivity|].
      split; [exact HC7|]. split; [lia|]. repeat (split; [assumption|]). exact C3s11.
    + exists fx', pos, S1, regs7, mem7, md7. split; [reflexivity|].
      split; [exact HC7|]. split; [lia|]. repeat (split; [assumption|]). exact C3s11.
    + exists fx', pos, S1, regs7, mem7, md7. split; [reflexivity|]. exact HC7.
  - (* the bit clear: block B to the next head or the tail *)
    assert (A10' : getr regs2 10 = w64 0) by (rewrite A10, (dc_land_clear mask i Hi3 Hbit); reflexivity).
    eapply SRr_bind.
    { refine (@dcb_B fq rc SK B LAWS _ _ _ _ _ _ _ _ _ _ _ S1 W1 regs2 mem2 md2 i Hi3 HJ2 A10' _ _ _).
      - rewrite <- H27. dc_kr Hk2.
      - rewrite <- H23. dc_kr Hk2.
      - rewrite <- H26. dc_kr Hk2. }
    intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hk3 & Hio3 & Hm3 & Hp3 & (B27 & B23 & B26)).
    apply SRr_ret.
    assert (Hst : RateCsv.csv_prefix mask (S i) = RateCsv.csv_prefix mask i) by exact (dc_step_clear mask i Hbit).
    assert (Hm31 : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W1) mem3 a = aview rsegs (w_H W1) mem1 a)
      by (intros a Ha; rewrite (Hm3 a Ha ltac:(tauto)); exact (Hm2 a Ha ltac:(tauto))).
    assert (HC3 : @dc_core fx rc SK B c (S i) pos fq S1 W1 regs3 mem3 md3).
    { apply (@dc_carry fx rc SK B LAWS IMG c i (S i) pos fq fq S1 W1 regs1 mem1 md1 regs3 mem3 md3 Hpre HC
        ltac:(lia) Hfxk HJ3 (same_io_trans _ _ _ Hio2 Hio3)).
      - intros a Ha _ _ _. exact (Hm31 a Ha).
      - intros a Hpa. apply Hp3. apply Hp2. exact Hpa.
      - rewrite (dc_keep_reg _ _ _ _ Hk3) by reflexivity. dc_kr Hk2.
      - rewrite (dc_keep_reg _ _ _ _ Hk3) by reflexivity. dc_kr Hk2.
      - rewrite (dc_keep_reg _ _ _ _ Hk3) by reflexivity. dc_kr Hk2.
      - rewrite (dc_keep_reg _ _ _ _ Hk3) by reflexivity. dc_kr Hk2.
      - rewrite (dc_keep_reg _ _ _ _ Hk3) by reflexivity. dc_kr Hk2.
      - rewrite (dc_keep_reg _ _ _ _ Hk3) by reflexivity. dc_kr Hk2.
      - fold mask. rewrite Hst. rewrite (dc_keep_reg _ _ _ _ Hk3) by reflexivity.
        rewrite (dc_keep_reg _ _ _ _ Hk2) by reflexivity. exact G21.
      - fold mask F. rewrite Hst. apply (dc_garr8_kept _ mem1 mem3 _ _ Htmp). intros x Hx. apply Hm31.
        rewrite length_app in Hx. cbn [length] in Hx. lia. }
    assert (K13 : getr regs3 13 = w64 (2 ^ 64 - 1 - (F + 32)))
      by (rewrite (dc_keep_reg _ _ _ _ Hk3) by reflexivity; rewrite (dc_keep_reg _ _ _ _ Hk2) by reflexivity; exact H13).
    assert (K22 : getr regs3 22 = w64 44100)
      by (rewrite (dc_keep_reg _ _ _ _ Hk3) by reflexivity; rewrite (dc_keep_reg _ _ _ _ Hk2) by reflexivity; exact H22).
    assert (K24 : getr regs3 24 = w64 96000)
      by (rewrite (dc_keep_reg _ _ _ _ Hk3) by reflexivity; rewrite (dc_keep_reg _ _ _ _ Hk2) by reflexivity; exact H24).
    assert (K25 : getr regs3 25 = w64 SNP_FMT)
      by (rewrite (dc_keep_reg _ _ _ _ Hk3) by reflexivity; rewrite (dc_keep_reg _ _ _ _ Hk2) by reflexivity; exact H25).
    destruct i as [|[|[|i]]]; [| | | lia].
    + exists fq, pos, S1, regs3, mem3, md3. split; [reflexivity|].
      split; [exact HC3|]. split; [lia|]. repeat (split; [assumption|]). exact B27.
    + exists fq, pos, S1, regs3, mem3, md3. split; [reflexivity|].
      split; [exact HC3|]. split; [lia|]. repeat (split; [assumption|]). exact B27.
    + exists fq, pos, S1, regs3, mem3, md3. split; [reflexivity|]. exact HC3.
Qed.
End main.

Print Assumptions dc_body.
