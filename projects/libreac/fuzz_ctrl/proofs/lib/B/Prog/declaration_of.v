From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcDecl RcDeclLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFPLib asan_memcpy_c declaration_of_c.
Import ListNotations.
Open Scope Z_scope.

(* The ubsan proof (lib/U/Prog/declaration_of.v) with the checks of this build: each load of the row and each store
   to the 32 bytes at o first reads the shadow byte of its address (s1 holds the shadow offset) and goes on when it is
   0 or above the address's offset in its 8-byte granule; addressable m 296 and o 32 give that, so the
   __asan_report_* paths are not reached. The UBSan checks (m mod 8, no wrap of o + j) do not trap. The two copies
   are __asan_memcpy (asan_memcpy_c.v). *)

Lemma da_Rw : forall x : word, 0 <= bv_unsigned x < 2^64.
Proof. intros x. exact (zr_word x). Qed.

Lemma da_addr_sub : forall m p n k n', addressable m p n -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  addressable m (p + k) n'.
Proof.
  intros m p n k n' (H1 & H2 & H3 & H) Hk Hn' Hkn. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p + k + i) with (p + (k + i)) by lia. apply H. lia.
Qed.

Lemma da_app_mid : forall a t, app_mem a -> app_mem (a + 32) -> 0 <= t <= 32 -> app_mem (a + t).
Proof. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros a t H1 H2 Ht. lia. Qed.

(* The shadow and the runtime's cells [RT_LO, RT_HI) are outside the footprint: the window K below sp (above
   HIGHMEM_BEG) and the 32 bytes at o (application memory, apart from the runtime's cells). *)
Lemma da_so_g : forall m lo sp o, HIGHMEM_BEG <= lo -> lo + 2256 <= sp -> addressable m o 32 -> app_mem (o + 32) ->
  forall x, in_shadow x -> outside [(sp - 2256, sp); (o, o + 32)] x.
Proof.
  intros m lo sp o HHM LO (_ & _ & _ & HA) HAP x Hx. cbn [outside].
  split; [unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia|].
  split; [|exact I].
  intros H. destruct (HA 0 ltac:(lia)) as [A0 _]. rewrite Z.add_0_r in A0.
  pose proof (da_app_mid o (x - o) A0 HAP ltac:(lia)) as A.
  replace (o + (x - o)) with x in A by lia.
  revert A Hx. unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. lia.
Qed.

Lemma da_ro_g : forall lo sp o, HIGHMEM_BEG <= lo -> lo + 2256 <= sp -> (o + 32 <= RT_LO \/ RT_HI <= o) ->
  forall x, RT_LO <= x < RT_HI -> outside [(sp - 2256, sp); (o, o + 32)] x.
Proof.
  intros lo sp o HHM LO Ho x Hx. cbn [outside]. unfold RT_LO, RT_HI, HIGHMEM_BEG in *.
  split; [lia|]. split; [lia | exact I].
Qed.

(* The check byte: `neg` and `sb` store the low 8 bits of - s. *)
Lemma da_negc' : forall s, le1 (Z_to_bv 64 (0 - s)) = [Z_to_bv 8 ((256 - s mod 256) mod 256)].
Proof.
  intros s. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. rewrite mod_mod8_of_modw by lia. change (2^8) with 256.
  Z.div_mod_to_equations. lia.
Qed.

Lemma da_negc : forall s, 0 <= s < 2^64 ->
  le1 (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 s))) = [Z_to_bv 8 ((256 - s mod 256) mod 256)].
Proof. intros s Hs. rewrite (unsigned_lit s) by lia. apply da_negc'. Qed.

Section DB.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mw ow : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo : Z) (row ob : list byte) (off : Z).
Hypothesis MCPY : asan_memcpy_contract.
Hypothesis LO : lo + 2256 <= bv_unsigned sp.
Hypothesis HLEN : length row = 296%nat.
Hypothesis HM8 : bv_unsigned mw mod 8 = 0.
Hypothesis DMO : bv_unsigned ow + 32 <= bv_unsigned mw \/ bv_unsigned mw + 296 <= bv_unsigned ow.
Hypothesis DMS : bv_unsigned mw + 296 <= bv_unsigned sp - 2256 \/ bv_unsigned sp <= bv_unsigned mw.
Hypothesis DOS : bv_unsigned ow + 32 <= bv_unsigned sp - 2256 \/ bv_unsigned sp <= bv_unsigned ow.
Hypothesis HCE : asan_cells m0.
Hypothesis HSW : shadow_rw m0.
Hypothesis HHM : HIGHMEM_BEG <= lo.
Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
Hypothesis HADm : addressable m0 (bv_unsigned mw) 296.
Hypothesis HADo : addressable m0 (bv_unsigned ow) 32.
Hypothesis HAPo : app_mem (bv_unsigned ow + 32).
Hypothesis HRTo : bv_unsigned ow + 32 <= RT_LO \/ RT_HI <= bv_unsigned ow.

(* The footprint: the window K below sp and the 32 bytes at o. *)
Definition Wd : list ivl := [(bv_unsigned sp - 2256, bv_unsigned sp); (bv_unsigned ow, bv_unsigned ow + 32)].

(* The shadow bytes of the 296 bytes at m and of the 32 bytes at o, read in m0 with the offset off that s1 holds. *)
Hypothesis HSRm : asan_shadow_rd rsegs m0 off (bv_unsigned mw) 296 Wd.
Hypothesis HAAm : asan_addressable rsegs m0 off (bv_unsigned mw) 296.
Hypothesis HSRo : asan_shadow_rd rsegs m0 off (bv_unsigned ow) 32 Wd.
Hypothesis HAAo : asan_addressable rsegs m0 off (bv_unsigned ow) 32.

Definition Qd : machine_state -> Prop :=
  declaration_of_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mw ow F fc m0 lo row ob.

Definition FC (j : list byte) : list cell :=
  [CB 8 j; C8 s1; C8 s0; C8 ra].

Definition D (mc : word -> option byte) (P : list byte) : Prop :=
  exists j, oinv rsegs (bv_unsigned sp + -32) (FC j) lo (bv_unsigned sp - 2256) (bv_unsigned sp) m0 mc
              (bv_unsigned mw) row (bv_unsigned ow) P.

Lemma da_lo : HIGHMEM_BEG <= lo /\ HIGHMEM_BEG = 0x10007fff8000.
Proof. split; [exact HHM | reflexivity]. Qed.

Lemma da_app_o : forall t, 0 <= t <= 32 -> app_mem (bv_unsigned ow + t).
Proof.
  intros t Ht. pose proof HADo as (_ & _ & _ & HA). destruct (HA 0 ltac:(lia)) as [A0 _]. rewrite Z.add_0_r in A0.
  exact (da_app_mid _ t A0 HAPo Ht).
Qed.

Lemma da_app_m : forall t, 0 <= t < 296 -> app_mem (bv_unsigned mw + t).
Proof. intros t Ht. pose proof HADm as (_ & _ & _ & HA). exact (proj1 (HA t Ht)). Qed.

Lemma da_so : forall x, in_shadow x -> outside Wd x.
Proof. exact (da_so_g m0 lo (bv_unsigned sp) (bv_unsigned ow) HHM LO HADo HAPo). Qed.

Lemma da_ro : forall x, RT_LO <= x < RT_HI -> outside Wd x.
Proof. exact (da_ro_g lo (bv_unsigned sp) (bv_unsigned ow) HHM LO HRTo). Qed.

(* The runtime's cells and the shadow are outside Wd: a run that writes only Wd keeps them. *)
Lemma da_rt : forall mc, munch Wd m0 mc -> wmono rsegs m0 mc -> asan_cells mc /\ shadow_rw mc.
Proof.
  intros mc MU WM. split.
  - exact (fl_asan_cells Wd m0 mc HCE MU da_ro).
  - exact (fl_shadow_rw Wd m0 mc HSW MU WM da_so).
Qed.

(* The check of the byte X = A + j (A = m or o) in a memory mc that the run reached writing only Wd: the shadow byte
   k is readable and passes the 1-byte check (0, or above X mod 8). *)
Lemma da_shadow : forall mc A n X j, munch Wd m0 mc ->
  asan_shadow_rd rsegs m0 off A n Wd -> asan_addressable rsegs m0 off A n -> 0 <= j < n -> X = A + j ->
  exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + off)) 1 = Some [k]
                   /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros mc A n X j MU HSR HAD Hj ->.
  pose proof (asan_shadow_rd_munch rsegs m0 mc off A n Wd Wd HSR MU (fun x Hx => Hx)) as HR'.
  pose proof (asan_addressable_munch rsegs m0 mc off A n Wd Wd HAD HSR MU (fun x Hx => Hx)) as HA'.
  destruct (asan_shadow_read rsegs mc off A n Wd j HR' Hj) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [exact (HA' j k Hj BK) | apply rc_byte_signed].
Qed.

(* The 4-byte check of the load at m + j (j = 16, 20): the shadow byte k passes (0, or above X mod 8 + 3). *)
Lemma da_shadow4 : forall mc X j, munch Wd m0 mc -> 0 <= j -> j + 4 <= 296 -> j mod 8 + 4 <= 8 ->
  X = bv_unsigned mw + j ->
  exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + off)) 1 = Some [k]
                   /\ (bv_signed k = 0 \/ X mod 8 + 3 < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros mc X j MU Hj Hj4 Hm ->.
  pose proof (asan_shadow_rd_munch rsegs m0 mc off _ 296 Wd Wd HSRm MU (fun x Hx => Hx)) as HR'.
  pose proof (asan_addressable_munch rsegs m0 mc off _ 296 Wd Wd HAAm HSRm MU (fun x Hx => Hx)) as HA'.
  destruct (asan_shadow_read rsegs mc off _ 296 Wd j HR' ltac:(lia)) as (k & RK & BK).
  assert (EM : (bv_unsigned mw + j) mod 8 = j mod 8).
  { rewrite Z.add_mod, HM8 by lia. rewrite Z.add_0_l. apply Z.mod_mod. lia. }
  exists k. split; [exact RK|]. split; [|apply rc_byte_signed].
  pose proof (asan_check_lt rsegs mc off _ 296 j 4 k HA' Hj ltac:(lia) Hj4 ltac:(rewrite EM; lia) BK) as OK.
  lia.
Qed.

(* The state of the run: oinv (lib/Prog/RcDeclLib.v) of the 32-byte frame and the window K. *)
Lemma DF0 : forall j, bv_unsigned sp + -32 + Z.of_nat (cells_size (FC j)) <= bv_unsigned ow \/
                      bv_unsigned ow + 32 <= bv_unsigned sp + -32.
Proof. intros j. unfold FC. cbn [cells_size csize Nat.add]. lia. Qed.

Lemma DR0 : bv_unsigned mw + Z.of_nat (length row) <= bv_unsigned ow \/ bv_unsigned ow + 32 <= bv_unsigned mw.
Proof. rewrite HLEN. lia. Qed.

Lemma D_ok : forall mc P k, D mc P -> k = Z.of_nat (length P) -> (length P < 32)%nat ->
  store_ok rsegs mc (wa (bv_unsigned ow + k)) 1 = true.
Proof. intros mc P k [j DD] Hk Hl. exact (oinv_ok rsegs _ _ _ _ _ _ mc _ _ _ P k DD Hk Hl). Qed.

Lemma D_okw : forall mc P (x : word), D mc P -> bv_unsigned x = bv_unsigned ow + Z.of_nat (length P) ->
  (length P < 32)%nat -> store_ok rsegs mc x 1 = true.
Proof. intros mc P x [j DD] Hx Hl. exact (oinv_okw rsegs _ _ _ _ _ _ mc _ _ _ P x DD Hx Hl). Qed.

Lemma D_store : forall mc P (A v : word) b, D mc P -> (length P < 32)%nat ->
  A = wa (bv_unsigned ow + Z.of_nat (length P)) -> le1 v = [b] -> D (write_to_mem mc A (le1 v)) (P ++ [b]).
Proof.
  intros mc P A v b [j DD] Hl HA Hb. exists j.
  exact (oinv_store rsegs _ _ _ _ _ _ mc _ _ _ P A v b DD Hl (DF0 j) DR0 HA Hb).
Qed.

Lemma D_target : forall mc P n, D mc P -> (length P + n <= 32)%nat ->
  exists junk, rw_cells rsegs mc (bv_unsigned ow + Z.of_nat (length P)) [CB n junk].
Proof. intros mc P n [j DD] Hn. exact (oinv_target rsegs _ _ _ _ _ _ mc _ _ _ P n DD Hn). Qed.

Lemma D_rd : forall mc P i, D mc P -> (i < length P)%nat ->
  ov_read_bytes rsegs mc (wa (bv_unsigned ow + Z.of_nat i)) 1 = Some [nth i P (Z_to_bv 8 0)].
Proof. intros mc P i [j DD] Hi. exact (oinv_rd rsegs _ _ _ _ _ _ mc _ _ _ P i DD Hi). Qed.

Lemma D_row : forall mc P, D mc P -> bytes_at rsegs mc (bv_unsigned mw) row.
Proof. intros mc P [j DD]. exact (oinv_row rsegs _ _ _ _ _ _ mc _ _ _ P DD). Qed.

Lemma D_mi : forall mc P, D mc P -> mem_inv rsegs mc.
Proof. intros mc P [j DD]. exact (oinv_mem_inv rsegs _ _ _ _ _ _ mc _ _ _ P DD). Qed.

Lemma D_bound : forall mc P, D mc P -> 0 <= bv_unsigned ow /\ bv_unsigned ow + 32 <= 2^64 /\ (length P <= 32)%nat.
Proof. intros mc P [j DD]. exact (oinv_bound rsegs _ _ _ _ _ _ mc _ _ _ P DD). Qed.

Lemma D_mu : forall mc P, D mc P -> munch Wd m0 mc.
Proof. intros mc P [j (_ & _ & MU & _)]. exact MU. Qed.

Lemma D_wm : forall mc P, D mc P -> wmono rsegs m0 mc.
Proof. intros mc P [j (_ & _ & _ & WM & _)]. exact WM. Qed.

Lemma D_stk : forall mc P, D mc P -> stk rsegs mc lo (bv_unsigned sp + -32).
Proof. intros mc P [j (_ & ST & _)]. exact ST. Qed.

Lemma D_final : forall mc P, D mc P -> length P = 32%nat ->
  exists j, rw_cells rsegs mc (bv_unsigned sp + -32) (FC j) /\ stk rsegs mc lo (bv_unsigned sp + -32) /\
    munch Wd m0 mc /\ wmono rsegs m0 mc /\ mem_inv rsegs mc /\ bytes_at rsegs mc (bv_unsigned mw) row /\
    rw_cells rsegs mc (bv_unsigned ow) [CB 32 P].
Proof. intros mc P [j DD] HP. exists j. exact (oinv_final rsegs _ _ _ _ _ _ mc _ _ _ P DD HP). Qed.

(* A call of __asan_memcpy: it writes the n bytes at o + |P| and its window of K bytes below the call's
   sp = sp - 32. *)
Lemma D_call : forall mc m' P new K, D mc P -> (length P + length new <= 32)%nat -> 0 <= K <= 2224 ->
  munch [(bv_unsigned ow + Z.of_nat (length P), bv_unsigned ow + Z.of_nat (length P) + Z.of_nat (length new));
         (bv_unsigned sp + -32 - K, bv_unsigned sp + -32)] mc m' ->
  wmono rsegs mc m' -> mem_inv rsegs m' -> bytes_at rsegs m' (bv_unsigned ow + Z.of_nat (length P)) new ->
  stk rsegs m' lo (bv_unsigned sp + -32) ->
  D m' (P ++ new).
Proof.
  intros mc m' P new K [j (FR & ST & MU & WM & MI & HR & WR & HL & rest & HLr & HB)] Hn HK MUc WMc MIc HN STc.
  pose proof WR as (HO0 & HO1 & _). pose proof (da_Rw sp) as Rsp. pose proof da_lo as HL0.
  pose proof (bytes_at_bound rsegs mc _ _ HR) as HRd. rewrite HLEN in HRd.
  exists j.
  split.
  { eapply rw_cells_transport; [exact FR | exact MUc | exact WMc |].
    unfold FC. cbn [disjoint_from cells_size csize Nat.add]. split; [lia|]. split; [lia | exact I]. }
  split; [exact STc|].
  split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
    intros z Hz. cbn [outside] in *. destruct Hz as (Hz1 & Hz2 & _). split; [lia|]. split; [lia | exact I]. }
  split; [eapply wmono_trans; eassumption|].
  split; [exact MIc|].
  split.
  { eapply bytes_at_transport; [exact HR | exact MUc |]. cbn [disjoint_from]. rewrite HLEN.
    split; [lia|]. split; [lia | exact I]. }
  split; [eapply wr_at_transport; eassumption|].
  split; [rewrite length_app; lia|].
  exists (skipn (length new) rest). split; [rewrite length_skipn, length_app; lia|].
  apply bytes_at_app in HB as [HBP HBr].
  rewrite <- app_assoc. apply bytes_at_app. split.
  - eapply bytes_at_transport; [exact HBP | exact MUc |]. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
  - apply bytes_at_app. split; [exact HN|].
    pose proof (rc_bytes_sub rsegs mc (bv_unsigned ow + Z.of_nat (length P)) rest (length new)
                  (length rest - length new) HBr ltac:(lia)) as HS.
    rewrite firstn_all2 in HS by (rewrite length_skipn; lia).
    eapply bytes_at_transport; [exact HS | exact MUc |]. cbn [disjoint_from]. rewrite length_skipn.
    split; [lia|]. split; [lia | exact I].
Qed.

Lemma D_init : forall mc j, rw_cells rsegs mc (bv_unsigned sp + -32) (FC j) ->
  stk rsegs mc lo (bv_unsigned sp + -32) ->
  munch Wd m0 mc -> wmono rsegs m0 mc -> mem_inv rsegs mc -> bytes_at rsegs mc (bv_unsigned mw) row ->
  rw_cells rsegs mc (bv_unsigned ow) [CB 32 ob] -> D mc [].
Proof.
  intros mc j FR ST MU WM MI HR HO. exists j.
  eapply oinv_init; [exact FR | exact ST | exact MU | exact WM | exact MI | exact HR | exact HO].
Qed.

(* +0xc4 .. +0xd4: the epilogue. *)
Lemma epi : forall mc res ob' j rac t0c t1c t2c s0c s1c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c,
  rw_cells rsegs mc (bv_unsigned sp + -32) (FC j) ->
  stk rsegs mc lo (bv_unsigned sp + -32) ->
  munch Wd m0 mc -> wmono rsegs m0 mc -> mem_inv rsegs mc -> bytes_at rsegs mc (bv_unsigned mw) row ->
  rw_cells rsegs mc (bv_unsigned ow) [CB 32 ob'] ->
  res = (if decl_ok row then 1 else 0) -> ob' = (if decl_ok row then decl row else ob) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0c t1c t2c s0c s1c (Z_to_bv 64 res)
                     a1c a2c a3c a4c a5c a6c a7c s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                 F (Z_to_bv 64 0x831d8) fc None mc (seg_rom rsegs)).
Proof.
  intros mc res ob' j rac t0c t1c t2c s0c s1c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c
    FR ST MU WM MI HR HO -> ->.
  destruct (da_rt mc MU WM) as [AC SR].
  pose proof (da_Rw sp) as Rsp.
  unfold FC in FR.
  do 4 step.
  release_frame FR ST (bv_unsigned sp).
  step.
  apply evt_done. unfold Qd, declaration_of_post, DECLARATION_OF_K.
  do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact HO|].
  split; [exact HR|]. split; [exact AC | exact SR].
Qed.

(* A call __asan_memcpy(o + |P|, m + k, n), 1 <= n, |P| + n <= 32, |P| <= 25, k + n < 296, k + 8 <= 296. *)
Lemma o_memcpy : forall mc P (k n : nat) (x y z : word) retpc s0c s1c s2c s3c s4c s5c s6c s7c t0c t1c t2c
    a3c a4c a5c a6c a7c t3c t4c t5c t6c,
  D mc P -> (0 < n)%nat -> (length P + n <= 32)%nat -> (length P <= 25)%nat -> (k + n < 296)%nat ->
  (k + 8 <= 296)%nat -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
  bv_unsigned x = bv_unsigned ow + Z.of_nat (length P) -> bv_unsigned y = bv_unsigned mw + Z.of_nat k ->
  bv_unsigned z = Z.of_nat n ->
  (forall m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     D m' (P ++ firstn n (skipn k row)) ->
     evt rsegs Qd (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' s0c s1c x
                         a1' a2' a3' a4' a5' a6' a7' s2c s3c s4c s5c s6c s7c s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 retpc) fc None m' (seg_rom rsegs))) ->
  evt rsegs Qd (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0c t1c t2c s0c s1c x y z
                      a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7c s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
Proof.
  intros mc P k n x y z retpc s0c s1c s2c s3c s4c s5c s6c s7c t0c t1c t2c a3c a4c a5c a6c a7c t3c t4c t5c t6c
    DD Hn0 Hn H25 Hk Hk8 Hr He Ex Ey Ez K.
  pose proof (da_Rw ow) as Row. pose proof (da_Rw mw) as Rmw. pose proof (da_Rw sp) as Rsp.
  pose proof (D_bound mc P DD) as OB. pose proof da_lo as HL0.
  pose proof (D_row mc P DD) as HR.
  pose proof (bytes_at_bound rsegs mc _ _ HR) as HRb. rewrite HLEN in HRb. change (Z.of_nat 296) with 296 in HRb.
  pose proof (rc_bytes_sub rsegs mc (bv_unsigned mw) row k n HR ltac:(lia)) as HS.
  destruct (D_target mc P n DD Hn) as [junk RW].
  assert (LS : length (firstn n (skipn k row)) = n)
    by (rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia]).
  pose proof (D_mu mc P DD) as MU. pose proof (D_wm mc P DD) as WM.
  destruct (da_rt mc MU WM) as [AC SR].
  pose proof (fl_addressable Wd m0 mc _ _ HADo MU da_so) as AO.
  pose proof (fl_addressable Wd m0 mc _ _ HADm MU da_so) as AM.
  assert (ES : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  pose proof MCPY as HM. unfold asan_memcpy_contract, ASAN_MEMCPY_K in HM. cbv zeta in HM.
  eapply evt_cut.
  { eapply HM with (src := firstn n (skipn k row)) (junk := junk) (lo := lo).
    all: rewrite ?ES, ?Ex, ?Ey, ?Ez, ?Nat2Z.id.
    - exact HS.
    - exact LS.
    - exact RW.
    - lia.
    - lia.
    - apply (da_addr_sub mc _ 296); [exact AM | lia | lia | lia].
    - apply (da_addr_sub mc _ 32); [exact AO | lia | lia | lia].
    - right. replace (bv_unsigned mw + Z.of_nat k + Z.of_nat n) with (bv_unsigned mw + (Z.of_nat k + Z.of_nat n))
        by lia. apply da_app_m. lia.
    - right. replace (bv_unsigned ow + Z.of_nat (length P) + Z.of_nat n)
        with (bv_unsigned ow + (Z.of_nat (length P) + Z.of_nat n)) by lia. apply da_app_o. lia.
    - right. split.
      + replace (bv_unsigned mw + Z.of_nat k + 7) with (bv_unsigned mw + (Z.of_nat k + 7)) by lia.
        apply da_app_m. lia.
      + replace (bv_unsigned ow + Z.of_nat (length P) + 7) with (bv_unsigned ow + (Z.of_nat (length P) + 7)) by lia.
        apply da_app_o. lia.
    - lia.
    - lia.
    - lia.
    - exact (D_stk mc P DD).
    - lia.
    - exact HHM.
    - lia.
    - exact AC.
    - exact SR.
    - exact (D_mi mc P DD). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              -> & MUc & WMc & MIc & STc & RWc & _ & _ & _).
  rewrite ES, Ex, Ez in MUc. rewrite ES in STc. rewrite Ex, Ez, Nat2Z.id in RWc.
  rewrite (ret_pc_even retpc) by lia.
  destruct (rc_cb_rw rsegs m' _ _ _ RWc) as (HB & HL & _).
  apply K. eapply (D_call mc m' P _ 2224); [exact DD | rewrite LS; exact Hn | lia | | exact WMc | exact MIc
    | exact HB | exact STc].
  rewrite LS. exact MUc.
Qed.

Ltac steps_to P :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
  | _ => step; steps_to P
  end.

Ltac steps_until_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

(* A shadow check of the byte X: `srli; add s1; lb` reads its shadow byte k (SH gives k, its read and the check
   fact), then `bnez` goes on when k = 0; else the slow path `andi r, X, 7` (and for a 4-byte load `addi r, r, 3`,
   the tactic `extra`) and `blt r, k` goes on as the check passes. The register r is generalized at the join, and
   the call of __asan_report_* is not reached. *)
Ltac chk_go X r SH extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  step; rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
  step; step; clear RK; steps_until_if;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evt segs Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7; extra X;
          step;
          first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k))
                    by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
                  replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia)
                | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k))
                    by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
                  replace (X mod 8 + 3 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia) ];
          bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac no_extra X := idtac.
Ltac add3 X := step; rewrite ?(unsigned_lit (X mod 8)) by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia).

(* The check at pc P (the srli) of the byte m + j. *)
Ltac chkm P j r :=
  steps_to P;
  lazymatch goal with
  | DD : D ?mc _ |- _ =>
      let MU := fresh "MU" in pose proof (D_mu mc _ DD) as MU;
      chk_go (bv_unsigned mw + j) r
        (da_shadow mc (bv_unsigned mw) 296 (bv_unsigned mw + j) j MU HSRm HAAm ltac:(lia) eq_refl) no_extra;
      clear MU
  end.

(* The 4-byte check at pc P of the load at m + j. *)
Ltac chkm4 P j r :=
  steps_to P;
  lazymatch goal with
  | DD : D ?mc _ |- _ =>
      let MU := fresh "MU" in pose proof (D_mu mc _ DD) as MU;
      chk_go (bv_unsigned mw + j) r
        (da_shadow4 mc (bv_unsigned mw + j) j MU ltac:(lia) ltac:(lia) ltac:(lia) eq_refl) add3;
      clear MU
  end.

(* The check at pc P of the byte X = o + j. *)
Ltac chko P X j r :=
  steps_to P;
  lazymatch goal with
  | DD : D ?mc _ |- _ =>
      let MU := fresh "MU" in pose proof (D_mu mc _ DD) as MU;
      chk_go X r (da_shadow mc (bv_unsigned ow) 32 X j MU HSRo HAAo ltac:(lia) ltac:(lia)) no_extra;
      clear MU
  end.

Ltac to_store mc :=
  step;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc _ _) _) => idtac
  | _ => to_store mc
  end.

Ltac byte_of v :=
  lazymatch v with
  | Z_to_bv 64 ?z => constr:(Z_to_bv 8 z)
  | zxb ?b => b
  end.

(* The store of byte k of o (P is the prefix written so far, |P| = k). *)
Ltac ost k :=
  lazymatch goal with
  | DD : D ?mc ?P |- _ =>
      let HS := fresh "HS" in
      lazymatch k with
      | 0 => pose proof (D_okw mc P ow DD ltac:(cbn [length Z.of_nat]; lia) ltac:(cbn [length]; lia)) as HS
      | _ => pose proof (D_ok mc P k DD ltac:(reflexivity) ltac:(cbn [length]; lia)) as HS
      end;
      to_store mc; clear HS;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?A (le1 ?v)) _) =>
          let b := byte_of v in
          let D' := fresh "D" in
          assert (D' : D (write_to_mem mc A (le1 v)) (P ++ [b]))
            by (apply (D_store mc P A v b DD);
                [ cbn [length]; lia
                | first [ reflexivity
                        | unfold wa; cbn [length Z.of_nat]; rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self
                        | unfold wa; f_equal; cbn [length Z.of_nat]; lia ]
                | first [apply rc_le1_lit; lia | apply le1_zxb]]);
          cbn [app] in D'; clear DD;
          let mc' := fresh "mc" in
          set (mc' := write_to_mem mc A (le1 v)) in *; clearbody mc'
      end
  end.

Ltac rrow k :=
  lazymatch goal with
  | DD : D ?mc _ |- _ =>
      let HR := fresh "HR" in
      pose proof (rd_byte rsegs mc (bv_unsigned mw) row k (D_row mc _ DD) ltac:(rewrite HLEN; lia)) as HR;
      let z := eval cbv in (Z.of_nat k) in change (Z.of_nat k) with z in HR
  end.

Ltac len_tac := rewrite ?length_app, ?head_len, ?repeat_length, ?runs_len by lia; cbn [length]; lia.

(* A UBSan check: the branch to the `unimp` at 0x83534 is not taken. *)
Ltac uchk := step; unfold bv_ltu; fold_lit_ux; if_false.

Ltac ltf := rewrite rc_ltu_lit by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; cbv iota.

Ltac nrm8 := rewrite (unsigned_lit (bv_unsigned ow + 8)) by lia; rewrite (zb_lxor_ones (bv_unsigned ow + 8)) by lia.

(* The store of a slot byte at x = o + |P| (the address register holds Z_to_bv 64 x). *)
Ltac lsto x :=
  lazymatch goal with
  | DD : D ?mc ?P |- _ =>
      let HS := fresh "HS" in
      pose proof (D_okw mc P (Z_to_bv 64 x) DD ltac:(rewrite unsigned_lit by lia; len_tac) ltac:(len_tac)) as HS;
      to_store mc; clear HS;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?A (le1 ?v)) _) =>
          let b := byte_of v in
          let D' := fresh "D" in
          assert (D' : D (write_to_mem mc A (le1 v)) (P ++ [b]))
            by (apply (D_store mc P A v b DD);
                [ len_tac
                | first [ reflexivity | unfold wa; f_equal; len_tac
                        | unfold wa; cbn [length Z.of_nat]; rewrite Z.add_0_r; symmetry; apply Z_to_bv_lit_self ]
                | first [apply rc_le1_lit; lia | apply le1_zxb]]);
          cbn [app] in D'; clear DD;
          let mc' := fresh "mc" in
          set (mc' := write_to_mem mc A (le1 v)) in *; clearbody mc'
      end
  end.

(* +0x3f8 .. +0x41c: the check and store of the check byte at o + 31, then a0 = 1 and the epilogue. *)
Lemma fin31 : forall mc ic oc rac t0c t1c t2c a0c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c,
  gfacts row ic oc -> D mc (gram_pre row) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0c t1c t2c ow (Z_to_bv 64 off) a0c
                      (Z_to_bv 64 (psum (gram_pre row) 31)) a2c a3c a4c a5c a6c a7c
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x8350c) fc None mc (seg_rom rsegs)).
Proof.
  intros mc ic oc rac t0c t1c t2c a0c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c G DD.
  destruct (gfacts_ok row ic oc HLEN G) as (OK & DE & LP & _).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw sp) as Rsp. pose proof (D_bound _ _ DD) as OB.
  pose proof (psum_range (gram_pre row) 31) as PR. change (Z.of_nat 31) with 31 in PR.
  step. uchk.
  chko 0x83518 (bv_unsigned ow + 31) 31 (Z_to_bv 5 13).
  pose proof (D_ok mc (gram_pre row) 31 DD ltac:(rewrite LP; reflexivity) ltac:(lia)) as HS.
  step. step. clear HS.
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?A (le1 ?v)) _) =>
      assert (D' : D (write_to_mem mc A (le1 v)) (gram_pre row ++ [check_byte (gram_pre row)]))
        by (apply (D_store mc (gram_pre row) A v _ DD);
            [ lia
            | unfold wa; rewrite LP; first [reflexivity | f_equal; lia]
            | unfold check_byte; first [apply da_negc; lia | apply da_negc'] ]);
      set (mc' := write_to_mem mc A (le1 v)) in *; clearbody mc'
  end.
  step. step.
  destruct (D_final _ _ D' ltac:(rewrite length_app, LP; reflexivity)) as (j & FR & ST & MU & WM & MI & HRw & HO).
  eapply epi; [exact FR | exact ST | exact MU | exact WM | exact MI | exact HRw | exact HO
              | rewrite OK; reflexivity | rewrite OK, DE; reflexivity].
Qed.

(* +0x3c0 .. +0x3e4: the sum loop over o .. o + 30, each address checked for wrap (UBSan) and each load checked
   (ASan). *)
Lemma sumloop : forall n i mc ic oc rac t0c t1c t2c a0c a5c a6c a7c t3c t4c t5c t6c,
  (i + n = 31)%nat -> (0 < n)%nat -> gfacts row ic oc -> D mc (gram_pre row) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0c t1c t2c ow (Z_to_bv 64 off) a0c
                      (Z_to_bv 64 (psum (gram_pre row) i)) (Z_to_bv 64 (Z.of_nat i))
                      (Z_to_bv 64 (18446744073709551615 - bv_unsigned ow)) (Z_to_bv 64 31) a5c a6c a7c
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x834d4) fc None mc (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros i mc ic oc rac t0c t1c t2c a0c a5c a6c a7c t3c t4c t5c t6c Hin Hn G DD; [lia|].
  destruct (gfacts_ok row ic oc HLEN G) as (OK & DE & LP & _).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw sp) as Rsp. pose proof (D_bound _ _ DD) as OB.
  pose proof (D_rd _ _ i DD ltac:(lia)) as HR.
  pose proof (psum_range (gram_pre row) i) as PR.
  step. ltf.
  chko 0x834dc (bv_unsigned ow + Z.of_nat i) (Z.of_nat i) (Z_to_bv 5 16).
  step. step. step. rewrite psum_S_zxb.
  step. rewrite rc_eqb_lit by lia.
  destruct n as [|n].
  - replace (Z.of_nat i + 1 =? 31) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. cbv iota. replace i with 30%nat in * by lia.
    step.
    eapply fin31; eassumption.
  - replace (Z.of_nat i + 1 =? 31) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. cbv iota.
    replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
    apply (IH (S i) mc ic oc); [lia | lia | exact G | exact DD].
Qed.

(* +0x394 .. +0x3bc: __asan_memcpy(o + 20, m + 254, 11), then the sum loop's start. *)
Lemma tailcp : forall mc ic oc rac t0c t1c t2c a1c a3c a4c a5c a6c a7c t3c t4c t5c t6c,
  gfacts row ic oc -> D mc (gram_head row ++ slot_bytes (box_lay row) (ic / 4) (oc / 4)) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0c t1c t2c ow (Z_to_bv 64 off) mw
                      a1c (Z_to_bv 64 (bv_unsigned ow + 8)) a3c a4c a5c a6c a7c
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x834a8) fc None mc (seg_rom rsegs)).
Proof.
  intros mc ic oc rac t0c t1c t2c a1c a3c a4c a5c a6c a7c t3c t4c t5c t6c G DD.
  destruct (gfacts_ok row ic oc HLEN G) as (OK & DE & LP & EP).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw mw) as Rmw. pose proof (da_Rw sp) as Rsp.
  pose proof (D_bound _ _ DD) as OB.
  assert (LH : length (gram_head row ++ slot_bytes (box_lay row) (ic / 4) (oc / 4)) = 20%nat).
  { pose proof LP as L. rewrite EP, length_app in L. rewrite firstn_length_le in L by (rewrite length_skipn, HLEN; lia).
    lia. }
  pose proof (D_row _ _ DD) as HRw.
  pose proof (bytes_at_bound rsegs mc _ _ HRw) as HRb. rewrite HLEN in HRb. change (Z.of_nat 296) with 296 in HRb.
  step. step. unfold bv_ltu. fold_lit_ux. rewrite (unsigned_lit (bv_unsigned ow + 8)) by lia. if_false.
  step. step. step. step. step.
  eapply (o_memcpy mc _ 254 11); [exact DD | lia | lia | lia | lia | lia | lia | reflexivity
         | rewrite unsigned_lit by lia; rewrite LH; reflexivity
         | rewrite unsigned_lit by lia; reflexivity | reflexivity |].
  intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' D'.
  rewrite <- EP in D'.
  step. step. step. rewrite (zb_lxor_ones (bv_unsigned ow)) by lia. step.
  apply (sumloop 31 0 m' ic oc); [lia | lia | exact G | exact D'].
Qed.

(* +0x35c .. +0x380: the slots k .. 11 get 3. *)
Lemma loop5 : forall n (j : nat) mc ic oc rac t0c t1c t2c a1c a6c t3c t4c t5c t6c,
  gfacts row ic oc -> (j + n = Z.to_nat (12 - (ic / 4 + oc / 4)))%nat -> (0 < n)%nat ->
  D mc (gram_head row ++ runs (box_lay row) (ic / 4) (oc / 4) ++ repeat (Z_to_bv 8 3) j) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0c t1c t2c ow (Z_to_bv 64 off) mw
                      a1c (Z_to_bv 64 (bv_unsigned ow + 8)) (Z_to_bv 64 (18446744073709551615 - (bv_unsigned ow + 8)))
                      (Z_to_bv 64 3) (Z_to_bv 64 12) a6c (Z_to_bv 64 (ic / 4 + oc / 4 + Z.of_nat j))
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x83470) fc None mc (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros j mc ic oc rac t0c t1c t2c a1c a6c t3c t4c t5c t6c G Hj Hn DD; [lia|].
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw sp) as Rsp.
  pose proof (D_bound _ _ DD) as OB.
  step. ltf.
  chko 0x83478 (bv_unsigned ow + 8 + (ic / 4 + oc / 4 + Z.of_nat j)) (8 + (ic / 4 + oc / 4 + Z.of_nat j))
    (Z_to_bv 5 5).
  lsto (bv_unsigned ow + 8 + (ic / 4 + oc / 4 + Z.of_nat j)).
  rewrite <- !app_assoc, rc_repeat_snoc in *.
  step. rewrite rc_eqb_lit by lia.
  destruct n as [|n].
  - replace (ic / 4 + oc / 4 + Z.of_nat j + 1 =? 12) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. cbv iota. step.
    apply (tailcp _ ic oc); [exact G|].
    rewrite slot_runs. replace (Z.to_nat (12 - ic / 4 - oc / 4)) with (S j) by lia.
    assumption.
  - replace (ic / 4 + oc / 4 + Z.of_nat j + 1 =? 12) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. cbv iota.
    replace (ic / 4 + oc / 4 + Z.of_nat j + 1) with (ic / 4 + oc / 4 + Z.of_nat (S j)) by lia.
    apply (IH (S j) _ ic oc); [exact G | lia | lia | assumption].
Qed.

(* +0x344 .. +0x358: k <= 11 goes to the 3-loop, else to the tail copy. *)
Lemma threes : forall mc ic oc rac t0c t1c t2c a1c a3c a4c a5c a6c t3c t4c t5c t6c,
  gfacts row ic oc -> D mc (gram_head row ++ runs (box_lay row) (ic / 4) (oc / 4)) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0c t1c t2c ow (Z_to_bv 64 off) mw
                      a1c (Z_to_bv 64 (bv_unsigned ow + 8)) a3c a4c a5c a6c (Z_to_bv 64 (ic / 4 + oc / 4))
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x83458) fc None mc (seg_rom rsegs)).
Proof.
  intros mc ic oc rac t0c t1c t2c a1c a3c a4c a5c a6c t3c t4c t5c t6c G DD.
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw sp) as Rsp.
  pose proof (D_bound _ _ DD) as OB.
  step. rewrite rc_sextw by lia. step. step. rewrite rc_lts_lit by lia.
  destruct (Z.ltb_spec 11 (ic / 4 + oc / 4)) as [E12|E12]; cbv iota.
  - apply (tailcp _ ic oc); [exact G|]. rewrite slot_runs.
    replace (Z.to_nat (12 - ic / 4 - oc / 4)) with 0%nat by lia. cbn [repeat]. rewrite app_nil_r. exact DD.
  - step. nrm8. step. step.
    replace (Z_to_bv 64 (ic / 4 + oc / 4)) with (Z_to_bv 64 (ic / 4 + oc / 4 + Z.of_nat 0)) by (f_equal; lia).
    apply (loop5 (Z.to_nat (12 - (ic / 4 + oc / 4))) 0 _ ic oc); [exact G | lia | lia |].
    cbn [repeat]. rewrite app_nil_r. exact DD.
Qed.

(* +0x2ac .. +0x2d8 (box_lay = 1): the a input slots get 0. *)
Lemma loop3 : forall n (j : nat) mc ic oc rac t0c t1c t2c a1c a6c t3c t4c t5c t6c,
  gfacts row ic oc -> box_lay row = 1 -> (j + n = Z.to_nat (ic / 4))%nat -> (0 < n)%nat ->
  D mc (gram_head row ++ repeat (Z_to_bv 8 1) (Z.to_nat (oc / 4)) ++ repeat (Z_to_bv 8 0) j) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0c t1c t2c ow (Z_to_bv 64 off) mw
                      a1c (Z_to_bv 64 (bv_unsigned ow + 8)) (Z_to_bv 64 (oc / 4 + Z.of_nat j))
                      (Z_to_bv 64 (ic / 4 - Z.of_nat j)) (Z_to_bv 64 (18446744073709551615 - (bv_unsigned ow + 8)))
                      a6c (Z_to_bv 64 (oc / 4 + Z.of_nat j))
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x833c0) fc None mc (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros j mc ic oc rac t0c t1c t2c a1c a6c t3c t4c t5c t6c G HL Hj Hn DD; [lia|].
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw sp) as Rsp.
  pose proof (D_bound _ _ DD) as OB.
  step. ltf.
  chko 0x833c8 (bv_unsigned ow + 8 + (oc / 4 + Z.of_nat j)) (8 + (oc / 4 + Z.of_nat j)) (Z_to_bv 5 5).
  lsto (bv_unsigned ow + 8 + (oc / 4 + Z.of_nat j)).
  rewrite <- !app_assoc, rc_repeat_snoc in *.
  step. rewrite rc_addiw_dec by lia. step. step. step. rewrite rc_eqbz by lia.
  destruct n as [|n].
  - replace (ic / 4 - Z.of_nat j - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. cbv iota. step.
    replace (Z_to_bv 64 (oc / 4 + Z.of_nat j + 1)) with (Z_to_bv 64 (ic / 4 + oc / 4)) by (f_equal; lia).
    apply (threes _ ic oc); [exact G|]. unfold runs. rewrite HL, Z.eqb_refl.
    replace (Z.to_nat (ic / 4)) with (S j) by lia. assumption.
  - replace (ic / 4 - Z.of_nat j - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. cbv iota.
    replace (oc / 4 + Z.of_nat j + 1) with (oc / 4 + Z.of_nat (S j)) by lia.
    replace (ic / 4 - Z.of_nat j - 1) with (ic / 4 - Z.of_nat (S j)) by lia.
    apply (IH (S j) _ ic oc); [exact G | exact HL | lia | lia | assumption].
Qed.

(* +0x304 .. +0x330 (box_lay <> 1): the b output slots get 1. *)
Lemma loop4 : forall n (j : nat) mc ic oc rac t1c t2c a1c a6c t3c t4c t5c t6c,
  gfacts row ic oc -> box_lay row <> 1 -> (j + n = Z.to_nat (oc / 4))%nat -> (0 < n)%nat ->
  D mc (gram_head row ++ repeat (Z_to_bv 8 2) (Z.to_nat (ic / 4)) ++ repeat (Z_to_bv 8 1) j) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp
                      (Z_to_bv 64 (18446744073709551615 - (bv_unsigned ow + 8))) t1c t2c ow (Z_to_bv 64 off) mw
                      a1c (Z_to_bv 64 (bv_unsigned ow + 8)) (Z_to_bv 64 (ic / 4 + Z.of_nat j)) (Z_to_bv 64 1)
                      (Z_to_bv 64 (oc / 4 - Z.of_nat j)) a6c (Z_to_bv 64 (ic / 4 + Z.of_nat j))
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x83418) fc None mc (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros j mc ic oc rac t1c t2c a1c a6c t3c t4c t5c t6c G HL Hj Hn DD; [lia|].
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw sp) as Rsp.
  pose proof (D_bound _ _ DD) as OB.
  assert (HL' : (box_lay row =? 1) = false) by (apply Z.eqb_neq; exact HL).
  step. ltf.
  chko 0x83420 (bv_unsigned ow + 8 + (ic / 4 + Z.of_nat j)) (8 + (ic / 4 + Z.of_nat j)) (Z_to_bv 5 6).
  lsto (bv_unsigned ow + 8 + (ic / 4 + Z.of_nat j)).
  rewrite <- !app_assoc, rc_repeat_snoc in *.
  step. rewrite rc_addiw_dec by lia. step. step. step. rewrite rc_eqbz by lia.
  destruct n as [|n].
  - replace (oc / 4 - Z.of_nat j - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. cbv iota. step.
    replace (Z_to_bv 64 (ic / 4 + Z.of_nat j + 1)) with (Z_to_bv 64 (ic / 4 + oc / 4)) by (f_equal; lia).
    apply (threes _ ic oc); [exact G|]. unfold runs. rewrite HL'.
    replace (Z.to_nat (oc / 4)) with (S j) by lia. assumption.
  - replace (oc / 4 - Z.of_nat j - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb]. cbv iota.
    replace (ic / 4 + Z.of_nat j + 1) with (ic / 4 + Z.of_nat (S j)) by lia.
    replace (oc / 4 - Z.of_nat j - 1) with (oc / 4 - Z.of_nat (S j)) by lia.
    apply (IH (S j) _ ic oc); [exact G | exact HL | lia | lia | assumption].
Qed.

(* +0x298 .. +0x2a8 (box_lay = 1): after the outputs, ic = 0 goes to the 3s, else to the 0-loop. *)
Lemma p27c : forall mc ic oc rac t0c t1c t2c a1c a5c a6c t3c t4c t5c t6c,
  gfacts row ic oc -> box_lay row = 1 -> D mc (gram_head row ++ repeat (Z_to_bv 8 1) (Z.to_nat (oc / 4))) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0c t1c t2c ow (Z_to_bv 64 off) mw
                      a1c (Z_to_bv 64 (bv_unsigned ow + 8)) (Z_to_bv 64 ic) (Z_to_bv 64 (ic / 4)) a5c a6c
                      (Z_to_bv 64 (oc / 4)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x833ac) fc None mc (seg_rom rsegs)).
Proof.
  intros mc ic oc rac t0c t1c t2c a1c a5c a6c t3c t4c t5c t6c G HL DD.
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof G as (HO & HI & HOC & Ric & Roc & Mic & Moc & Hab).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw sp) as Rsp.
  pose proof (D_bound _ _ DD) as OB.
  step. rewrite rc_eqbz by lia. destruct (Z.eqb_spec ic 0) as [E0|E0]; cbv iota.
  - assert (Ea : ic / 4 = 0) by (rewrite E0; reflexivity).
    replace (Z_to_bv 64 (oc / 4)) with (Z_to_bv 64 (ic / 4 + oc / 4)) by (rewrite Ea; reflexivity).
    apply (threes _ ic oc); [exact G|]. unfold runs. rewrite HL, Z.eqb_refl, Ea. cbn [Z.to_nat repeat].
    rewrite app_nil_r. exact DD.
  - step. rewrite rc_sextw by lia. step. step. rewrite rc_seqz_add by lia. step. nrm8.
    replace (Z_to_bv 64 (oc / 4)) with (Z_to_bv 64 (oc / 4 + Z.of_nat 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (ic / 4)) with (Z_to_bv 64 (ic / 4 - Z.of_nat 0)) by (f_equal; lia).
    apply (loop3 (Z.to_nat (ic / 4)) 0 _ ic oc); [exact G | exact HL | lia | lia |].
    cbn [repeat]. rewrite app_nil_r. exact DD.
Qed.

(* +0x2f0 .. +0x300 (box_lay <> 1): after the inputs, oc = 0 goes to the 3s, else to the 1-loop. *)
Lemma p2b4 : forall mc ic oc rac t1c t2c a1c a3c a4c t3c t4c t5c t6c,
  gfacts row ic oc -> box_lay row <> 1 -> D mc (gram_head row ++ repeat (Z_to_bv 8 2) (Z.to_nat (ic / 4))) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp
                      (Z_to_bv 64 (18446744073709551615 - (bv_unsigned ow + 8))) t1c t2c ow (Z_to_bv 64 off) mw
                      a1c (Z_to_bv 64 (bv_unsigned ow + 8)) a3c a4c (Z_to_bv 64 (oc / 4)) (Z_to_bv 64 oc)
                      (Z_to_bv 64 (ic / 4)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x83404) fc None mc (seg_rom rsegs)).
Proof.
  intros mc ic oc rac t1c t2c a1c a3c a4c t3c t4c t5c t6c G HL DD.
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof G as (HO & HI & HOC & Ric & Roc & Mic & Moc & Hab).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw sp) as Rsp.
  pose proof (D_bound _ _ DD) as OB.
  assert (HL' : (box_lay row =? 1) = false) by (apply Z.eqb_neq; exact HL).
  step. rewrite rc_eqbz by lia. destruct (Z.eqb_spec oc 0) as [E0|E0]; cbv iota.
  - assert (Eb : oc / 4 = 0) by (rewrite E0; reflexivity).
    replace (Z_to_bv 64 (ic / 4)) with (Z_to_bv 64 (ic / 4 + oc / 4)) by (rewrite Eb, Z.add_0_r; reflexivity).
    apply (threes _ ic oc); [exact G|]. unfold runs. rewrite HL', Eb. cbn [Z.to_nat repeat].
    rewrite app_nil_r. exact DD.
  - step. rewrite rc_sextw by lia. step. step. rewrite rc_seqz_add by lia. step.
    replace (Z_to_bv 64 (ic / 4)) with (Z_to_bv 64 (ic / 4 + Z.of_nat 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (oc / 4)) with (Z_to_bv 64 (oc / 4 - Z.of_nat 0)) by (f_equal; lia).
    apply (loop4 (Z.to_nat (oc / 4)) 0 _ ic oc); [exact G | exact HL | lia | lia |].
    cbn [repeat]. rewrite app_nil_r. exact DD.
Qed.

(* +0x20c .. +0x230 (box_lay = 1): the b output slots get 1. *)
Lemma loop1 : forall n (j : nat) mc ic oc rac t1c t2c a1c t3c t4c t5c t6c,
  gfacts row ic oc -> box_lay row = 1 -> (j + n = Z.to_nat (oc / 4))%nat -> (0 < n)%nat ->
  D mc (gram_head row ++ repeat (Z_to_bv 8 1) j) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp
                      (Z_to_bv 64 (18446744073709551615 - (bv_unsigned ow + 8))) t1c t2c ow (Z_to_bv 64 off) mw
                      a1c (Z_to_bv 64 (bv_unsigned ow + 8)) (Z_to_bv 64 ic) (Z_to_bv 64 (ic / 4)) (Z_to_bv 64 1)
                      (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 (oc / 4))
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x83320) fc None mc (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros j mc ic oc rac t1c t2c a1c t3c t4c t5c t6c G HL Hj Hn DD; [lia|].
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw sp) as Rsp.
  pose proof (D_bound _ _ DD) as OB.
  step. ltf.
  chko 0x83328 (bv_unsigned ow + 8 + Z.of_nat j) (8 + Z.of_nat j) (Z_to_bv 5 7).
  lsto (bv_unsigned ow + 8 + Z.of_nat j).
  rewrite <- !app_assoc, rc_repeat_snoc in *.
  step. rewrite rc_eqb_lit by lia.
  destruct n as [|n].
  - replace (oc / 4 =? Z.of_nat j + 1) with true by (symmetry; apply Z.eqb_eq; lia).
    cbv iota.
    apply (p27c _ ic oc); [exact G | exact HL |].
    replace (Z.to_nat (oc / 4)) with (S j) by lia. assumption.
  - replace (oc / 4 =? Z.of_nat j + 1) with false by (symmetry; apply Z.eqb_neq; lia).
    cbv iota. step.
    replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
    apply (IH (S j) _ ic oc); [exact G | exact HL | lia | lia | assumption].
Qed.

(* +0x25c .. +0x280 (box_lay <> 1): the a input slots get 2. *)
Lemma loop2 : forall n (j : nat) mc ic oc rac t1c t2c a1c t3c t4c t5c t6c,
  gfacts row ic oc -> box_lay row <> 1 -> (j + n = Z.to_nat (ic / 4))%nat -> (0 < n)%nat ->
  D mc (gram_head row ++ repeat (Z_to_bv 8 2) j) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp
                      (Z_to_bv 64 (18446744073709551615 - (bv_unsigned ow + 8))) t1c t2c ow (Z_to_bv 64 off) mw
                      a1c (Z_to_bv 64 (bv_unsigned ow + 8)) (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 2)
                      (Z_to_bv 64 (oc / 4)) (Z_to_bv 64 oc) (Z_to_bv 64 (ic / 4))
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x83370) fc None mc (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros j mc ic oc rac t1c t2c a1c t3c t4c t5c t6c G HL Hj Hn DD; [lia|].
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw sp) as Rsp.
  pose proof (D_bound _ _ DD) as OB.
  step. ltf.
  chko 0x83378 (bv_unsigned ow + 8 + Z.of_nat j) (8 + Z.of_nat j) (Z_to_bv 5 7).
  lsto (bv_unsigned ow + 8 + Z.of_nat j).
  rewrite <- !app_assoc, rc_repeat_snoc in *.
  step. rewrite rc_eqb_lit by lia.
  destruct n as [|n].
  - replace (ic / 4 =? Z.of_nat j + 1) with true by (symmetry; apply Z.eqb_eq; lia).
    cbv iota.
    apply (p2b4 _ ic oc); [exact G | exact HL |].
    replace (Z.to_nat (ic / 4)) with (S j) by lia. assumption.
  - replace (ic / 4 =? Z.of_nat j + 1) with false by (symmetry; apply Z.eqb_neq; lia).
    cbv iota. step.
    replace (Z.of_nat j + 1) with (Z.of_nat (S j)) by lia.
    apply (IH (S j) _ ic oc); [exact G | exact HL | lia | lia | assumption].
Qed.

(* +0xd8 .. +0x1f4: the checks, stores and UBSan wrap checks of the 8 header bytes, then the branch on box_lay. *)
Lemma succ : forall mc ic oc rac t0c t1c t2c a1c a2c a7c t3c t4c t5c t6c,
  gfacts row ic oc -> D mc [] ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0c t1c t2c ow (Z_to_bv 64 off) mw
                      a1c a2c (Z_to_bv 64 ic) (Z_to_bv 64 (ic / 4)) (Z_to_bv 64 (oc / 4)) (Z_to_bv 64 oc) a7c
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x831ec) fc None mc (seg_rom rsegs)).
Proof.
  intros mc ic oc rac t0c t1c t2c a1c a2c a7c t3c t4c t5c t6c G DD.
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof G as (HO & HI & HOC & Ric & Roc & Mic & Moc & Hab).
  pose proof (da_Rw ow) as Row. pose proof (da_Rw mw) as Rmw. pose proof (da_Rw sp) as Rsp.
  pose proof (D_bound _ _ DD) as OB.
  pose proof (bytes_at_bound rsegs mc _ _ (D_row _ _ DD)) as HRb. rewrite HLEN in HRb.
  change (Z.of_nat 296) with 296 in HRb.
  chko 0x831ec (bv_unsigned ow) 0 (Z_to_bv 5 12).
  chko 0x83200 (bv_unsigned ow + 3) 3 (Z_to_bv 5 17).
  ost 0. ost 1. ost 2. ost 3. uchk.
  chkm 0x83238 252 (Z_to_bv 5 17).
  rrow 252%nat.
  chko 0x8324c (bv_unsigned ow + 4) 4 (Z_to_bv 5 5).
  ost 4. uchk.
  chko 0x83270 (bv_unsigned ow + 5) 5 (Z_to_bv 5 17). ost 5. uchk.
  chko 0x83290 (bv_unsigned ow + 6) 6 (Z_to_bv 5 17). ost 6. uchk.
  chkm 0x832b0 253 (Z_to_bv 5 17).
  rrow 253%nat.
  chko 0x832c4 (bv_unsigned ow + 7) 7 (Z_to_bv 5 5). ost 7. uchk.
  chkm 0x832e8 290 (Z_to_bv 5 17).
  rrow 290%nat. step. step. step.
  match goal with D1 : D ?mc1 _ |- _ => change (D mc1 (gram_head row)) in D1 end.
  step. rewrite rc_zxb_eqb by lia.
  destruct (Z.eqb_spec (bv_unsigned (nth 290 row (Z_to_bv 8 0))) 1) as [EL|EL]; cbn [negb]; cbv iota.
  - assert (HL : box_lay row = 1) by exact EL.
    step. rewrite rc_eqbz by lia. destruct (Z.eqb_spec oc 0) as [E0|E0]; cbv iota.
    + step.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (oc / 4)) by (rewrite E0; reflexivity).
      apply (p27c _ ic oc); [exact G | exact HL |]. replace (Z.to_nat (oc / 4)) with 0%nat by (rewrite E0; reflexivity).
      cbn [repeat]. rewrite app_nil_r. assumption.
    + step. step. step. nrm8. step. rewrite rc_seqz_add by lia. step.
      apply (loop1 (Z.to_nat (oc / 4)) 0 _ ic oc); [exact G | exact HL | lia | lia |].
      cbn [repeat]. rewrite app_nil_r. assumption.
  - assert (HL : box_lay row <> 1) by exact EL.
    step. nrm8.
    step. rewrite rc_eqbz by lia. destruct (Z.eqb_spec ic 0) as [E0|E0]; cbv iota.
    + step.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (ic / 4)) by (rewrite E0; reflexivity).
      apply (p2b4 _ ic oc); [exact G | exact HL |]. replace (Z.to_nat (ic / 4)) with 0%nat by (rewrite E0; reflexivity).
      cbn [repeat]. rewrite app_nil_r. assumption.
    + step. step. step. rewrite rc_seqz_add by lia. step.
      apply (loop2 (Z.to_nat (ic / 4)) 0 _ ic oc); [exact G | exact HL | lia | lia |].
      cbn [repeat]. rewrite app_nil_r. assumption.
Qed.

Ltac fail_exit HN :=
  step; step;
  match goal with
  | FR : rw_cells _ _ (bv_unsigned sp + -32) _, ST : stk _ _ _ _, MU : munch _ _ _, WM : wmono _ _ _,
    MI : mem_inv _ _, HROW : bytes_at _ _ (bv_unsigned mw) _, HO : rw_cells _ _ (bv_unsigned ow) _ |- _ =>
      eapply epi; [exact FR | exact ST | exact MU | exact WM | exact MI | exact HROW | exact HO
                  | rewrite (dok_false row ltac:(assumption) HN); reflexivity
                  | rewrite (dok_false row ltac:(assumption) HN); reflexivity]
  end.

(* +0x0 .. +0xd4: the prologue, the UBSan alignment check of m, the shadow offset, the checks and loads of m + 288,
   m + 16, m + 20, the paths. *)
Lemma run : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk rsegs m0 lo (bv_unsigned sp) -> bytes_at rsegs m0 (bv_unsigned mw) row ->
  rw_cells rsegs m0 (bv_unsigned ow) [CB 32 ob] -> mem_inv rsegs m0 ->
  asan_rt rsegs m0 GOT_CELL_K CELL_K off Wd ->
  evt rsegs Qd (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 mw ow a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                      t3 t4 t5 t6)
                  F (Z_to_bv 64 DECLARATION_OF) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST HROW HO MI HRT.
  unfold DECLARATION_OF.
  pose proof (munch_refl Wd m0) as MU. unfold Wd in MU.
  pose proof (wmono_refl rsegs m0) as WM.
  pose proof (da_Rw sp) as Rsp. pose proof (da_Rw mw) as Ra0. pose proof (da_Rw ow) as Ra1.
  pose proof da_lo as HL0.
  pose proof (bytes_at_bound rsegs m0 _ _ HROW) as HRb. rewrite HLEN in HRb. change (Z.of_nat 296) with 296 in HRb.
  pose proof (rw_cells_bound rsegs m0 _ _ HO) as HOb. cbn [cells_size csize Nat.add] in HOb.
  change (Z.of_nat 32) with 32 in HOb.
  carve_frame 32%nat ST.
  do 5 step.
  replace (Z.land (bv_unsigned mw) 7) with 0
    by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; symmetry; exact HM8).
  step. if_false.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m0 m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  do 5 step.
  clear RG RC HRT HRT1.
  assert (D0 : D m1 []) by (eapply D_init; [exact FR | exact ST | exact MU | exact WM | exact MI | exact HROW
                                           | exact HO]).
  pose proof (rd_byte rsegs m1 (bv_unsigned mw) row 288 HROW ltac:(lia)) as R288.
  pose proof (rc_rd4 rsegs m1 (bv_unsigned mw) row 16 HROW ltac:(lia)) as R16.
  pose proof (rc_rd4 rsegs m1 (bv_unsigned mw) row 20 HROW ltac:(lia)) as R20.
  change (Z.of_nat 288) with 288 in R288. change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 20) with 20 in R20.
  pose proof (rc_u32le_range row 16) as U16. pose proof (rc_u32le_range row 20) as U20.
  pose proof (rc_s32_range _ U16) as S16.
  chkm 0x83140 288 (Z_to_bv 5 13).
  step. step.
  rewrite rc_zxb_eqb by lia.
  destruct (Z.eqb_spec (bv_unsigned (nth 288 row (Z_to_bv 8 0))) 0) as [EO|EO]; cbv iota.
  - step. step. step. step.
    eapply (o_memcpy _ [] 24 32); [exact D0 | lia | cbn [length]; lia | cbn [length]; lia | lia | lia | lia
      | reflexivity | cbn [length Z.of_nat]; lia | rewrite unsigned_lit by lia; reflexivity | reflexivity |].
    intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' D'.
    step.
    destruct (D_final _ _ D'
                ltac:(cbn [app]; rewrite firstn_length_le; [reflexivity | rewrite length_skipn, HLEN; lia]))
      as (j' & FR' & ST' & MU' & WM' & MI' & HR' & HO').
    eapply epi; [exact FR' | exact ST' | exact MU' | exact WM' | exact MI' | exact HR' | exact HO' | |].
    + unfold decl_ok, box_org, rval, rbyte. rewrite EO. reflexivity.
    + unfold decl_ok, decl, box_org, rval, rbyte, box_cfg. rewrite EO. reflexivity.
  - chkm4 0x8315c 16 (Z_to_bv 5 13).
    step. rewrite (rc_sx32 (u32le row 16) U16).
    step. rewrite rc_lts0 by lia.
    destruct (Z.ltb_spec (s32 (u32le row 16)) 0) as [EI|EI]; cbv iota.
    + assert (HN : ~ (0 <= box_ic row /\ 0 <= box_oc row /\ box_ic row mod 4 = 0 /\ box_oc row mod 4 = 0 /\
                      box_ic row / 4 + box_oc row / 4 <= 12)) by (intros (H1 & _); unfold box_ic in H1; lia).
      fail_exit HN.
    + chkm4 0x83178 20 (Z_to_bv 5 14).
      step. rewrite (rc_zx32 (u32le row 20) U20). do 6 step. step.
      rewrite rc_okmask by lia.
      destruct ((Z.land (u32le row 20) 18446744071562067971 =? 0) && (s32 (u32le row 16) mod 4 =? 0)) eqn:EM;
        cbn [negb]; cbv iota.
      * apply andb_prop in EM as [EM1 EM2]. apply Z.eqb_eq in EM1, EM2.
        apply rc_mask_zero in EM1 as [Hu Hm].
        assert (S32o : s32 (u32le row 20) = u32le row 20)
          by (unfold s32; rewrite (proj2 (Z.ltb_lt _ _) Hu); reflexivity).
        do 5 step. rewrite (rc_srli2 (u32le row 20)) by lia. rewrite (rc_srliw2 (s32 (u32le row 16))) by lia.
        assert (B4 : 0 <= u32le row 20 / 4 < 2^30) by (Z.div_mod_to_equations; lia).
        assert (B5 : 0 <= s32 (u32le row 16) / 4 < 2^30) by (Z.div_mod_to_equations; lia).
        rewrite rc_ltu_lit by lia.
        destruct (Z.ltb_spec 12 (u32le row 20 / 4 + s32 (u32le row 16) / 4)) as [E12|E12]; cbn [negb]; cbv iota.
        -- assert (HN : ~ (0 <= box_ic row /\ 0 <= box_oc row /\ box_ic row mod 4 = 0 /\ box_oc row mod 4 = 0 /\
                           box_ic row / 4 + box_oc row / 4 <= 12))
             by (intros (H1 & H2 & H3 & H4 & H5); unfold box_ic, box_oc in *; rewrite S32o in H5; lia).
           fail_exit HN.
        -- eapply (succ _ (s32 (u32le row 16)) (u32le row 20)); [|exact D0].
           split; [exact EO|]. split; [reflexivity|]. split; [unfold box_oc; exact S32o|].
           split; [lia|]. split; [lia|]. split; [exact EM2|]. split; [exact Hm|]. lia.
      * assert (HN : ~ (0 <= box_ic row /\ 0 <= box_oc row /\ box_ic row mod 4 = 0 /\ box_oc row mod 4 = 0 /\
                        box_ic row / 4 + box_oc row / 4 <= 12)).
        { intros (H1 & H2 & H3 & H4 & H5).
          assert (Hu : u32le row 20 < 2^31)
            by (revert H2; unfold box_oc, s32; destruct (Z.ltb_spec (u32le row 20) (2^31)); intros; lia).
          assert (S32o : s32 (u32le row 20) = u32le row 20)
            by (unfold s32; rewrite (proj2 (Z.ltb_lt _ _) Hu); reflexivity).
          unfold box_oc in H4. rewrite S32o in H4.
          pose proof (proj2 (rc_mask_zero row 20) (conj Hu H4)) as L.
          unfold box_ic in H3. rewrite L, H3 in EM. cbn in EM. discriminate EM. }
        fail_exit HN.
Qed.

End DB.

Theorem declaration_of_holds : asan_memcpy_contract -> declaration_of_contract.
Proof.
  intros MCPY. unfold declaration_of_contract, DECLARATION_OF_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo row ob
    ST LO HM8 HLEN HROW HO DMO DMS DOS MI HCE HSW HHM HAE HADm HADo HAPo HRTo.
  pose proof (da_so_g m lo (bv_unsigned sp) (bv_unsigned a1) HHM LO HADo HAPo) as SO.
  pose proof (da_ro_g lo (bv_unsigned sp) (bv_unsigned a1) HHM LO HRTo) as RO.
  pose proof (rt_shadow_rd m (bv_unsigned a0) 296 _ HADm SO) as HSRm.
  pose proof (rt_addressable m (bv_unsigned a0) 296 HADm) as HAAm.
  pose proof (rt_shadow_rd m (bv_unsigned a1) 32 _ HADo SO) as HSRo.
  pose proof (rt_addressable m (bv_unsigned a1) 32 HADo) as HAAo.
  pose proof (rt_asan_rt m _ HCE
                (fun x Hx => match Hx with
                             | or_introl H => RO x ltac:(unfold GOT_CELL_K, RT_LO, RT_HI in *; lia)
                             | or_intror (or_introl H) => RO x ltac:(unfold CELL_K, RT_LO, RT_HI in *; lia)
                             | or_intror (or_intror H) => SO x H
                             end)) as HRT.
  set (off := ASAN_K) in HSRm, HAAm, HSRo, HAAo, HRT. clearbody off.
  eapply run; eassumption.
Qed.

Ltac rowtac :=
  lazymatch goal with
  | |- exists row, image_bytes ?segs ?A ?n = Some row /\ _ =>
      let r := eval vm_compute in (image_bytes segs A n) in
      lazymatch r with
      | Some ?l => exists l; split; [vm_compute; reflexivity | split; vm_compute; reflexivity]
      end
  end.

Theorem declaration_of_rows_holds : declaration_of_rows.
Proof.
  unfold declaration_of_rows, BOX_CATALOGUE. intros i Hi.
  do 11 (destruct i as [|i]; [rowtac|]). lia.
Qed.
