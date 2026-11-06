From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_inflight_acked_c check_inflight_acked_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of check_inflight_acked_contract_F (image B, entry 0x85358, frame 16 bytes, 44 words), with StepF's step:
   each data access is closed from the rng premise of exactly the range it touches.

   The walk (listing DgnTransportBList.v, slots 4142-4185, AF_check_inflight_acked = 0x40b8):
     0x85358-0x8535c  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x85360-0x8536c  auipc a1; auipc a2; lw a1 (GOT.acked at 0x5e5038); addi a2: a2 = 0x5f2ce0, the base of OW.
     0x85370          lw a3,216(a2): OW.acked at 0x5f2db8.
     0x85374          blt a3,a1: the trap path when OW.acked < GOT.acked.
     0x85378-0x8537c  andi a1,a0,7; bnez a1: the UBSan alignment check of p, to the unimp word at 0x853e0.
     0x85380-0x85388  the 8-byte loads of GOT_CELL_K 0xa3cf0 and CELL_K 0xac678 (asan_cells): a3 = 0x7fff8000.
     0x8538c-0x8539c  a1 = p + 64; the shadow byte k of p + 64 (lb at ((p + 64) >> 3) + 0x7fff8000); bnez k.
     0x853e4-0x853ec  k <> 0: a5 = ((p + 64) & 7) + 3 and blt a5,k back to the load.
     0x853a0-0x853a8  lw a1,0(a1): n->counter; lw a4,224(a2): OW.acked_counter at 0x5f2dc0; bne a1,a4: trap path.
     0x853ac-0x853bc  a0 = p + 68; the shadow byte k of p + 68; bnez k.
     0x853f8-0x85400  k <> 0: a3 = ((p + 68) & 7) + 1 and blt a3,k back to the load.
     0x853c0-0x853c8  lhu a0,0(a0): n->retry; lw a1,228(a2): OW.acked_retry at 0x5f2dc4; bne a1,a0: trap path.
     0x853cc-0x853d4  ld ra,8(sp); addi sp,sp,16; ret.
   Why the other paths never run:
     - the trap path 0x853d8 / 0x853dc / 0x853e0 (__asan_handle_no_return, abort, the unimp word): the model premise
       check_inflight_acked_m Bw n = Some (Bw', tt) gives GOT_acked Bw <= OW_acked Bw, n_counter n =
       OW_acked_counter Bw and n_retry n = OW_acked_retry Bw (cia_model). By the world relation the four world loads
       read sub Bw A_.. 4 (tw_bytes_at), so their values are Z_to_bv 64 (s32_at Bw A_..) (lw_world). The loaded
       counter, sign-extended, is the same word as the loaded OW.acked_counter (EQC); the zero-extended 2-byte retry
       (n_retry n < 2^16) is the same word as the sign-extended OW.acked_retry (EQR). So no branch to the trap is
       taken from 0x85374, 0x853a8 or 0x853c8.
     - the branch at 0x8537c to the unimp word: p mod 8 = 0, so p & 7 = 0.
     - the error paths 0x853f4 (__asan_report_load4) and 0x85404 (__asan_report_load2): cia_shadow derives, from
       addressable m (p + 64) 4 / addressable m (p + 68) 2, that the shadow byte k is 0 or (a mod 8) + n - 1 < k, so
       the bnez falls through or the blt at 0x853ec / 0x85400 is taken back to the load.
   The world relation after the run: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_B_LO, G_HARNESS_B_HI) (off_stk premise), so tw_at holds of the same Bw (TMAP_B_kept).

   File shape, and why: the machine run is the lemma cia_walk, whose world words are four byte-list variables and
   four Z variables and whose post is a variable Q reached through a premise, so no goal a step converts holds a
   world term; cia_world reads the four words out of tw_at, cia_vals turns the model's two field facts into the
   words the loads leave, cia_post closes the contract's post, and the theorem is their composition.
   Every world field is named by the NUMERAL the load computes (65300, 65528, 65536, 65540), as the plain walk
   lib/Prog/T/check_inflight_acked.v:16-18 and :52-72 does: a conversion between an accessor and its definition at
   such an offset (there `change (OW_acked B) with (s32_at B 65528)`, here `unfold TW.OW_acked_counter` in the
   model fact) costs more than 20 s and the 24 GB cap at Qed, measured here with a Qed timeout on a 3-line lemma
   that did nothing else. The accessors are moved to the numerals by rewriting with cia_got / cia_ow / cia_owc /
   cia_owr, whose own proofs normalise the address with `replace .. by reflexivity` first. *)

(* ============================================================================
   Kit B's AsanKAProof.v is not on the base: the lemmas of lib/A/Prog/AsanKAProof.v this walk uses, over image B's
   rsegs, with the same proofs.
   ============================================================================ *)

Lemma cia_rd1 : forall m a b, mrd rsegs m (wa a) = Some b -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof. intros m a b H. rewrite ov_rdn, rdn_unfold, H. reflexivity. Qed.

Lemma cia_rdw0 : forall m (w : word) a b, mrd rsegs m (wa a) = Some b -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w 1 = Some [b].
Proof. intros m w a b H E. rewrite <- (Z_to_bv_bv_unsigned w), E. apply cia_rd1. exact H. Qed.

Lemma cia_mrd_tp : forall m m' lo hi a b, munch [(lo, hi)] m m' -> 0 <= a < 2^64 -> (a < lo \/ hi <= a) ->
  mrd rsegs m (wa a) = Some b -> mrd rsegs m' (wa a) = Some b.
Proof.
  intros m m' lo hi a b MU Ha Hd H. unfold mrd in *. rewrite MU; [exact H|].
  rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

Lemma cia_bytes_tp : forall m m' lo hi a bs, munch [(lo, hi)] m m' ->
  a + Z.of_nat (length bs) <= lo \/ hi <= a -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo hi a bs MU Hd H. eapply bytes_at_transport; [exact H | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma cia_signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2^64 / 2) with (2^63). Z.div_mod_to_equations. lia.
Qed.

Lemma cia_byte_signed_range : forall k : byte, -128 <= bv_signed k < 128.
Proof.
  intros k. pose proof (bv_signed_in_range 8 k ltac:(lia)) as R. unfold bv_half_modulus, bv_modulus in R.
  change (2 ^ Z.of_N 8 / 2) with 128 in R. lia.
Qed.

Lemma cia_sxb_eq0 : forall k : byte, bv_eqb (sxb k) (Z_to_bv 64 0) = (bv_signed k =? 0).
Proof.
  intros k. unfold sxb, bv_eqb. pose proof (cia_byte_signed_range k).
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  destruct (Z.eqb_spec (bv_signed k) 0) as [E|E].
  - rewrite E. reflexivity.
  - apply Z.eqb_neq. change (0 mod 2^64) with 0. Z.div_mod_to_equations. lia.
Qed.

Lemma cia_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. exact (Z.land_ones x 3 ltac:(lia)). Qed.

Ltac cia_gen_addi x w U := match goal with
  | |- context [Some (Z_to_bv 64 (bv_unsigned x + ?c))] =>
      let Ew := fresh "Ew" in
      assert (U : bv_unsigned (Z_to_bv 64 (bv_unsigned x + c)) = bv_unsigned x + c)
        by (apply unsigned_lit; first [lia | Z.div_mod_to_equations; lia]);
      remember (Z_to_bv 64 (bv_unsigned x + c)) as w eqn:Ew; clear Ew
  end.

Ltac cia_gen_shr x w U := match goal with
  | |- context [Some (Z_to_bv 64 (Z.shiftr (bv_unsigned x) 3))] =>
      let Ew := fresh "Ew" in
      assert (U : bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned x) 3)) = bv_unsigned x / 8)
        by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; apply unsigned_lit;
            pose proof (bv_unsigned_in_range 64 x) as Rx; unfold bv_modulus in Rx;
            change (2 ^ Z.of_N 64) with (2^64) in Rx;
            split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia);
      remember (Z_to_bv 64 (Z.shiftr (bv_unsigned x) 3)) as w eqn:Ew; clear Ew
  end.

(* ============================================================================
   The model, the loads, the shadow checks
   ============================================================================ *)

(* The model premise as the facts the three branches test. *)
Lemma cia_model : forall B n B', TC.check_inflight_acked_m B n = Some (B', tt) ->
  TW.GOT_acked B <= TW.OW_acked B /\ TI.n_counter n = TW.OW_acked_counter B /\
  TI.n_retry n = TW.OW_acked_retry B /\ B' = B.
Proof.
  intros B n B' HM. unfold TC.check_inflight_acked_m in HM.
  destruct (Z.ltb_spec (TW.OW_acked B) (TW.GOT_acked B)) as [E1|E1]; cbn [orb negb] in HM; [discriminate HM|].
  destruct (Z.eqb_spec (TI.n_counter n) (TW.OW_acked_counter B)) as [E2|E2]; cbn [orb negb] in HM;
    [|discriminate HM].
  destruct (Z.eqb_spec (TI.n_retry n) (TW.OW_acked_retry B)) as [E3|E3]; cbn [orb negb] in HM;
    [|discriminate HM].
  pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => B end) HM)
    as HB.
  cbv beta iota in HB.
  split; [lia|]. split; [exact E2|]. split; [exact E3|]. symmetry. exact HB.
Qed.

(* All the bytes bs at a, read at once. *)
Lemma cia_rd_all : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

(* The same read at a register value w whose number is a. *)
Lemma cia_rdw : forall m (w : word) a bs n, bytes_at rsegs m a bs -> length bs = n -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w n = Some bs.
Proof.
  intros m w a bs n H L E. rewrite <- (Z_to_bv_bv_unsigned w), E.
  change (Z_to_bv 64 a) with (wa a). apply cia_rd_all; assumption.
Qed.

(* The shadow byte that the check of an n-byte load at a reads (1 <= n <= 8), and the fact the check needs from it:
   it is 0, or larger than the offset of the access's last byte in a's 8-byte granule. *)
Lemma cia_shadow : forall m a n, 1 <= n <= 8 -> addressable m a n ->
  app_mem a /\ exists k, mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k /\
                         (bv_signed k = 0 \/ a mod 8 + (n - 1) < bv_signed k).
Proof.
  intros m a n Hn (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP & k & MK & _). rewrite Z.add_0_r in APP, MK.
  split; [exact APP|]. exists k. unfold shadow_addr in MK. split; [exact MK|].
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as MB.
  (* the last byte of [a, a + n) in a's granule: a + n - 1, or the granule's byte 7 when the range crosses *)
  set (i := Z.min (n - 1) (7 - a mod 8)).
  assert (Hi : 0 <= i < n) by (unfold i; lia).
  destruct (AB i Hi) as (_ & ki & MKi & SKi).
  assert (E : (a + i) / 8 = a / 8).
  { unfold i. clear - MB Hn P0. Z.div_mod_to_equations. lia. }
  unfold shadow_addr in MKi. rewrite E, MK in MKi. injection MKi as Ek. subst ki.
  assert (Em : (a + i) mod 8 = a mod 8 + i).
  { unfold i. clear - MB Hn P0. Z.div_mod_to_equations. lia. }
  unfold shadow_ok in SKi. rewrite Em in SKi. unfold i in SKi. lia.
Qed.

(* A shadow byte of an application address lies outside a 16-byte frame of application memory. *)
Lemma cia_shadow_tp : forall m m' lo hi a k, munch [(lo, hi)] m m' -> lo + 16 = hi ->
  app_mem lo -> app_mem (hi - 1) -> app_mem a ->
  mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k -> mrd rsegs m' (wa (a / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' lo hi a k MU E A1 A2 A3 H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2, A3. unfold ASAN_K in *.
  apply (cia_mrd_tp m m' lo hi _ k MU); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact H].
Qed.

(* The signed compare of a small non-negative value with a sign-extended shadow byte. *)
Lemma cia_lts_small : forall (x : Z) (k : byte), 0 <= x < 2^63 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (cia_byte_signed_range k).
  rewrite !cia_signed_lit by lia. reflexivity.
Qed.

(* blt on two sign-extended 32-bit values is the signed comparison of the values. *)
Lemma cia_lts : forall x y, -2^31 <= x < 2^31 -> -2^31 <= y < 2^31 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !cia_signed_lit by lia. reflexivity. Qed.

Lemma cia_swrap32 : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2^32 / 2) with (2^31). Z.div_mod_to_equations. lia.
Qed.

(* The image-B address of each world field the code loads, and its offset in the world as the NUMERAL the plain
   walk uses (lib/Prog/T/check_inflight_acked.v:52-72: 65300, 65528, 65536, 65540). Everything downstream names the
   field by that numeral: the plain walk's record says that a `change` between an accessor (OW_acked B) and its
   definition (s32_at B 65528) exhausted 24 GB at Qed, and a `reflexivity` between OW_acked_counter B and
   u_at B A_OW_acked_counter 4 did the same here (measured with a Qed timeout). *)
Lemma cia_got_addr : TB_GOT + 216 = 0x5e5038. Proof. reflexivity. Qed.
Lemma cia_got_off : TW.OFF_GOT + 216 = 65300. Proof. reflexivity. Qed.
Lemma cia_owa_addr : TB_OW + 216 = 0x5f2db8. Proof. reflexivity. Qed.
Lemma cia_owa_off : TW.OFF_OW + 216 = 65528. Proof. reflexivity. Qed.
Lemma cia_owc_addr : TB_OW + 224 = 0x5f2dc0. Proof. reflexivity. Qed.
Lemma cia_owc_off : TW.OFF_OW + 224 = 65536. Proof. reflexivity. Qed.
Lemma cia_owr_addr : TB_OW + 228 = 0x5f2dc4. Proof. reflexivity. Qed.
Lemma cia_owr_off : TW.OFF_OW + 228 = 65540. Proof. reflexivity. Qed.

(* The world's accessors at those numerals, in the plain walk's form (its cia_got / cia_ow / cia_owc / cia_owr). *)
Lemma cia_got : forall B, TW.s32_at B 65300 = TW.GOT_acked B.
Proof.
  intros B. unfold TW.GOT_acked, TW.A_GOT_acked, TW.OFF_GOT.
  replace (65084 + 216) with 65300 by reflexivity. reflexivity.
Qed.
Lemma cia_ow : forall B, TW.s32_at B 65528 = TW.OW_acked B.
Proof.
  intros B. unfold TW.OW_acked, TW.A_OW_acked, TW.OFF_OW.
  replace (65312 + 216) with 65528 by reflexivity. reflexivity.
Qed.
Lemma cia_owc : forall B, TW.u_at B 65536 4 = TW.OW_acked_counter B.
Proof.
  intros B. unfold TW.OW_acked_counter, TW.A_OW_acked_counter, TW.OFF_OW.
  replace (65312 + 224) with 65536 by reflexivity. reflexivity.
Qed.
Lemma cia_owr : forall B, TW.u_at B 65540 4 = TW.OW_acked_retry B.
Proof.
  intros B. unfold TW.OW_acked_retry, TW.A_OW_acked_retry, TW.OFF_OW.
  replace (65312 + 228) with 65540 by reflexivity. reflexivity.
Qed.

(* TWorldB's TMAP_B_kept at the leaf form's view: the kit states it over the raw view lambda, the statement file
   over csw_view. Unfolding csw_view here makes the two sides syntactically equal, so no caller has to convert
   between them. *)
Lemma cia_kept : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_B (csw_view m) Bw -> munch [(lo, hi)] m m' ->
  (hi <= TG.G_HARNESS_B_LO \/ TG.G_HARNESS_B_HI <= lo) ->
  tw_at TMAP_B (csw_view m') Bw.
Proof.
  intros m m' lo hi Bw H MU D. unfold csw_view in *.
  exact (TMAP_B_kept (segs:=rsegs) m m' lo hi Bw H MU D).
Qed.

(* ============================================================================
   The machine walk. The world's four byte lists and four values are variables, and the post is a variable Q
   reached through HQ: no goal a step converts holds a world term or tw_at.
   ============================================================================ *)

Lemma cia_walk :
  forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p lo cnt rty vGA vOA vOC vOR : Z)
         (bGA bOA bOC bOR : list byte),
    0 < p ->
    p mod 8 = 0 ->
    0 <= cnt < 2^32 ->
    0 <= rty < 2^16 ->
    bytes_at rsegs m (p + 64) (le4 (Z_to_bv 64 cnt)) ->
    bytes_at rsegs m (p + 68) (le2 (Z_to_bv 64 rty)) ->
    bytes_at rsegs m 0x5e5038 bGA -> length bGA = 4%nat ->
    bytes_at rsegs m 0x5f2db8 bOA -> length bOA = 4%nat ->
    bytes_at rsegs m 0x5f2dc0 bOC -> length bOC = 4%nat ->
    bytes_at rsegs m 0x5f2dc4 bOR -> length bOR = 4%nat ->
    sext 64 (bv_extract 0 32 (le_bytes_to_word bGA)) = Z_to_bv 64 vGA ->
    sext 64 (bv_extract 0 32 (le_bytes_to_word bOA)) = Z_to_bv 64 vOA ->
    sext 64 (bv_extract 0 32 (le_bytes_to_word bOC)) = Z_to_bv 64 vOC ->
    sext 64 (bv_extract 0 32 (le_bytes_to_word bOR)) = Z_to_bv 64 vOR ->
    -2^31 <= vGA < 2^31 -> -2^31 <= vOA < 2^31 -> vGA <= vOA ->
    sx32 (Z_to_bv 64 cnt) = Z_to_bv 64 vOC ->
    zx16 (Z_to_bv 64 rty) = Z_to_bv 64 vOR ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + 16 <= bv_unsigned sp ->
    off_stk sp 16 TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    asan_cells m ->
    app_mem (bv_unsigned sp - 16) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp 16 GOT_CELL_K 8 ->
    off_stk sp 16 CELL_K 8 ->
    off_stk sp 16 (p + 64) 4 -> addressable m (p + 64) 4 ->
    off_stk sp 16 (p + 68) 2 -> addressable m (p + 68) 2 ->
    ExecF.rng RNG (bv_unsigned sp - 16) 16 ->
    ExecF.rng RNG 0x5e5038 4 ->
    ExecF.rng RNG 0x5f2db8 4 ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (shadow_addr (p + 64)) 1 ->
    ExecF.rng RNG (p + 64) 4 ->
    ExecF.rng RNG 0x5f2dc0 4 ->
    ExecF.rng RNG (shadow_addr (p + 68)) 1 ->
    ExecF.rng RNG (p + 68) 2 ->
    ExecF.rng RNG 0x5f2dc4 4 ->
    (forall ms', (exists (a0' a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp)) -> Q ms') ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x85358) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p lo cnt rty vGA vOA vOC vOR bGA bOA bOC bOR HP0 HP8 RC HRT B64 B68 BGA LGA BOA LOA BOC LOC BOR LOR
    EGA EOA EOC EOR RvG RvA M1 EQC EQR ST HLO HOFF CELLS APW1 APW2 DGOT DCELL D64 A64 D68 A68
    RFR RGA ROA RGOT RCELL RS64 RF64 ROC RS68 RF68 ROR HQ.
  (* the shadow bytes of the two fields and what the checks need of them *)
  destruct (cia_shadow m (p + 64) 4 ltac:(lia) A64) as (APP64 & k64 & MK64 & SK64).
  destruct (cia_shadow m (p + 68) 2 ltac:(lia) A68) as (APP68 & k68 & MK68 & SK68).
  pose proof A64 as (_ & _ & E64 & _). pose proof A68 as (_ & _ & E68 & _). clear A64 A68.
  unfold off_stk in DGOT, DCELL, D64, D68.
  unfold GOT_CELL_K, CELL_K in DGOT, DCELL, RGOT, RCELL.
  unfold shadow_addr, ASAN_K in RS64, RS68.
  unfold APPMEM_END in E64, E68.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in HOFF.
  (* the argument register: p as a word, read back by the code *)
  remember (Z_to_bv 64 p) as a0 eqn:E0.
  assert (U0 : bv_unsigned a0 = p) by (subst a0; apply unsigned_lit; lia).
  clear E0. subst p.
  (* keep the bytes off transport_chunks: they are transported by hand past the ra store *)
  destruct CELLS as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (conj B64 (conj B68 (conj CK (conj GCK (conj BGA (conj BOA (conj BOC BOR))))))) as KEEP.
  clear B64 B68 CK GCK BGA BOA BOC BOR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x85358-0x8535c: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ =>
    rename MU' into MU1; first [constr_eq m1 m0 | rename m1 into m0] end.
  destruct KEEP as (B64 & B68 & CK & GCK & BGA & BOA & BOC & BOR).
  assert (B64' : bytes_at rsegs m0 (bv_unsigned a0 + 64) (le4 (Z_to_bv 64 cnt)))
    by (apply (cia_bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le4; lia | exact B64]).
  assert (B68' : bytes_at rsegs m0 (bv_unsigned a0 + 68) (le2 (Z_to_bv 64 rty)))
    by (apply (cia_bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le2; lia | exact B68]).
  assert (GCK0 : bytes_at rsegs m0 0xa3cf0 (le8 (wa 0xac678)))
    by (apply (cia_bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact GCK]).
  assert (CK0 : bytes_at rsegs m0 0xac678 (le8 (wa 0x7fff8000)))
    by (apply (cia_bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; lia | exact CK]).
  assert (BGA0 : bytes_at rsegs m0 0x5e5038 bGA)
    by (apply (cia_bytes_tp m m0 _ _ _ _ MU1); [rewrite LGA; lia | exact BGA]).
  assert (BOA0 : bytes_at rsegs m0 0x5f2db8 bOA)
    by (apply (cia_bytes_tp m m0 _ _ _ _ MU1); [rewrite LOA; lia | exact BOA]).
  assert (BOC0 : bytes_at rsegs m0 0x5f2dc0 bOC)
    by (apply (cia_bytes_tp m m0 _ _ _ _ MU1); [rewrite LOC; lia | exact BOC]).
  assert (BOR0 : bytes_at rsegs m0 0x5f2dc4 bOR)
    by (apply (cia_bytes_tp m m0 _ _ _ _ MU1); [rewrite LOR; lia | exact BOR]).
  clear B64 B68 CK GCK BGA BOA BOC BOR.
  pose proof (cia_shadow_tp m m0 _ _ _ k64 MU1 ltac:(lia) APW1 APW2 APP64 MK64) as M64.
  pose proof (cia_shadow_tp m m0 _ _ _ k68 MU1 ltac:(lia) APW1 APW2 APP68 MK68) as M68.
  unfold ASAN_K in M64, M68. clear MK64 MK68.
  (* 0x85360-0x8536c: a1 = GOT.acked; a2 = the base of OW *)
  pose proof (cia_rd_all m0 _ _ 4 BGA0 LGA) as R. step. step. step. clear R. step.
  rewrite EGA.
  (* 0x85370: a3 = OW.acked *)
  pose proof (cia_rd_all m0 _ _ 4 BOA0 LOA) as R. step. clear R.
  rewrite EOA.
  (* 0x85374: blt a3,a1 is not taken: GOT.acked <= OW.acked *)
  step. if_cases BR.
  { exfalso. rewrite (cia_lts vOA vGA RvA RvG) in BR. apply Z.ltb_lt in BR. lia. }
  (* 0x85378-0x8537c: a1 = p & 7; bnez a1 to the unimp word is not taken: p mod 8 = 0 *)
  step. step. if_cases BAL.
  { exfalso. zify_cond BAL. rewrite ?cia_land7 in BAL. clear - BAL HP8.
    first [ lia | rewrite ?Z.mod_mod in BAL by lia; lia | Z.div_mod_to_equations; lia ]. }
  (* 0x85380-0x85388: a3 = the shadow offset 0x7fff8000 *)
  pose proof (cia_rd_all m0 _ _ 8 GCK0 (length_le8 _)) as R. step. step. clear R.
  pose proof (cia_rd_all m0 _ _ 8 CK0 (length_le8 _)) as R. step. clear R.
  (* 0x8538c-0x8539c: the shadow byte of p + 64 *)
  step. cia_gen_addi a0 w64 U64.
  pose proof (rng_sub' _ _ _ (bv_unsigned w64) 4 RF64 ltac:(lia)) as RW64.
  step. cia_gen_shr w64 g64 G64. rewrite U64 in G64.
  step. cia_gen_addi g64 h64 H64.
  pose proof (rng_sub' _ _ _ (bv_unsigned h64) 1 RS64 ltac:(lia)) as RH64.
  pose proof (cia_rdw0 m0 h64 _ _ M64 ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 64) 8 ltac:(lia)) as MB64.
  destruct SK64 as [C|C];
    [ rewrite cia_sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
    | assert (C' : (bv_unsigned a0 + 64) mod 8 + 3 < bv_signed k64) by lia;
      rewrite cia_sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k64) 0) ltac:(lia)); cbn [negb];
      step; step; step;
      rewrite cia_land7, U64, (cia_lts_small ((bv_unsigned a0 + 64) mod 8 + 3) k64 ltac:(lia)),
        (proj2 (Z.ltb_lt _ _) C'); cbn [negb] ].
  (* 0x853a0-0x853a8: a1 = n->counter, a4 = OW.acked_counter, the same word *)
  all: pose proof (cia_rdw m0 w64 _ _ 4 B64' (length_le4 _) U64) as R; step; clear R.
  all: rewrite EQC.
  all: pose proof (cia_rd_all m0 _ _ 4 BOC0 LOC) as R; step; clear R.
  all: rewrite EOC.
  all: step; if_cases BR2; [exfalso; rewrite bv_eqb_refl in BR2; cbn [negb] in BR2; discriminate BR2 |].
  (* 0x853ac-0x853bc: the shadow byte of p + 68 *)
  all: step; cia_gen_addi a0 w68 U68.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w68) 2 RF68 ltac:(lia)) as RW68.
  all: step; cia_gen_shr w68 g68 G68.
  all: rewrite U68 in G68.
  all: step; cia_gen_addi g68 h68 H68.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h68) 1 RS68 ltac:(lia)) as RH68.
  all: pose proof (cia_rdw0 m0 h68 _ _ M68 ltac:(lia)) as R; step; clear R.
  all: step.
  all: pose proof (Z.mod_pos_bound (bv_unsigned a0 + 68) 8 ltac:(lia)) as MB68.
  all: destruct SK68 as [C2|C2];
    [ rewrite cia_sxb_eq0, (proj2 (Z.eqb_eq _ _) C2); cbn [negb]
    | assert (C2' : (bv_unsigned a0 + 68) mod 8 + 1 < bv_signed k68) by lia;
      rewrite cia_sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k68) 0) ltac:(lia)); cbn [negb];
      step; step; step;
      rewrite cia_land7, U68, (cia_lts_small ((bv_unsigned a0 + 68) mod 8 + 1) k68 ltac:(lia)),
        (proj2 (Z.ltb_lt _ _) C2'); cbn [negb] ].
  (* 0x853c0-0x853c8: a0 = n->retry, a1 = OW.acked_retry, the same word *)
  all: pose proof (cia_rdw m0 w68 _ _ 2 B68' (length_le2 _) U68) as R; step; clear R.
  all: rewrite EQR.
  all: pose proof (cia_rd_all m0 _ _ 4 BOR0 LOR) as R; step; clear R.
  all: rewrite EOR.
  all: step; if_cases BR3; [exfalso; rewrite bv_eqb_refl in BR3; cbn [negb] in BR3; discriminate BR3 |].
  (* 0x853cc-0x853d4: ld ra; addi sp; ret *)
  all: step; step; step.
  all: clear BGA0 BOA0 BOC0 BOR0 B64' B68' GCK0 CK0 LGA LOA LOC LOR EQC EQR EGA EOA EOC EOR M64 M68.
  all: apply evtF_done; apply HQ; do 7 eexists; split; [reflexivity|].
  all: split; [exact MU1|].
  all: split; [exact WM|].
  all: release_frame FR ST (bv_unsigned sp); exact ST.
Qed.

(* ============================================================================
   The contract: the model's facts, the world's bytes as raw memory (tw_bytes_at), the walk, and the world after
   the run (TMAP_B_kept).
   ============================================================================ *)

(* The four world words the code loads, as raw memory of image B, with their lengths, at the numerals. *)
Lemma cia_world : forall m Bw, tw_at TMAP_B (csw_view m) Bw ->
  (bytes_at rsegs m 0x5e5038 (TW.sub Bw 65300 4) /\ length (TW.sub Bw 65300 4) = 4%nat) /\
  (bytes_at rsegs m 0x5f2db8 (TW.sub Bw 65528 4) /\ length (TW.sub Bw 65528 4) = 4%nat) /\
  (bytes_at rsegs m 0x5f2dc0 (TW.sub Bw 65536 4) /\ length (TW.sub Bw 65536 4) = 4%nat) /\
  (bytes_at rsegs m 0x5f2dc4 (TW.sub Bw 65540 4) /\ length (TW.sub Bw 65540 4) = 4%nat).
Proof.
  intros m Bw HW.
  assert (LW : forall k, 0 <= k -> k + 4 <= TW.W_LEN -> length (TW.sub Bw k 4) = 4%nat).
  { intros k Hk Hk4. apply TWorldLemmas.length_sub; [exact Hk|].
    rewrite (tw_len TMAP_B _ Bw HW). unfold TW.W_LEN in *. lia. }
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_GOT TB_GOT TW.SZ_GOT 216 4 TMAP_B_ok HW TMAP_B_GOT
    ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)) as BGA.
  rewrite cia_got_addr, cia_got_off in BGA.
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 216 4 TMAP_B_ok HW TMAP_B_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as BOA.
  rewrite cia_owa_addr, cia_owa_off in BOA.
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 224 4 TMAP_B_ok HW TMAP_B_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as BOC.
  rewrite cia_owc_addr, cia_owc_off in BOC.
  pose proof (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 228 4 TMAP_B_ok HW TMAP_B_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as BOR.
  rewrite cia_owr_addr, cia_owr_off in BOR.
  split; [split; [exact BGA | apply LW; [lia | unfold TW.W_LEN; lia]]|].
  split; [split; [exact BOA | apply LW; [lia | unfold TW.W_LEN; lia]]|].
  split; [split; [exact BOC | apply LW; [lia | unfold TW.W_LEN; lia]]|].
  split; [exact BOR | apply LW; [lia | unfold TW.W_LEN; lia]].
Qed.

(* Ranges for the rewrites below, proved where no world term is in the context. *)
Lemma cia_r32 : forall z, 0 <= z < 2^32 -> 0 <= z < 2^64.
Proof. intros z Hz. lia. Qed.
Lemma cia_r16 : forall z, 0 <= z < 2^16 -> 0 <= z < 2^64.
Proof. intros z Hz. lia. Qed.
Lemma cia_r16s : forall z, 0 <= z < 2^16 -> -2^31 <= z < 2^31.
Proof. intros z Hz. lia. Qed.

(* The two fields of n, as the code loads them: the counter's 4 bytes load to the word at 65536, the retry's
   2 bytes (zero-extended) to the word at 65540; and the fields' bytes as the kit's le4 / le2. The accessors are
   moved to the numerals with cia_owc / cia_owr (rewrites), never by a conversion. *)
Lemma cia_vals : forall Bw (n : TI.ntc),
  TI.n_counter n = TW.OW_acked_counter Bw -> TI.n_retry n = TW.OW_acked_retry Bw -> 0 <= TI.n_retry n < 2 ^ 16 ->
  0 <= TI.n_counter n < 2^32 /\
  sx32 (Z_to_bv 64 (TI.n_counter n)) = Z_to_bv 64 (TW.s32_at Bw 65536) /\
  zx16 (Z_to_bv 64 (TI.n_retry n)) = Z_to_bv 64 (TW.s32_at Bw 65540) /\
  TW.put 4 (TI.n_counter n) = le4 (Z_to_bv 64 (TI.n_counter n)) /\
  TW.put 2 (TI.n_retry n) = le2 (Z_to_bv 64 (TI.n_retry n)).
Proof.
  intros Bw n CTR RTY HRT.
  rewrite <- (cia_owc Bw) in CTR. rewrite <- (cia_owr Bw) in RTY.
  assert (RC : 0 <= TI.n_counter n < 2^32).
  { rewrite CTR. exact (TWorldLemmas.u_at_range Bw 65536 4). }
  split; [exact RC|].
  split.
  { unfold sx32, TW.s32_at. rewrite (unsigned_lit _ (cia_r32 _ RC)). rewrite CTR. reflexivity. }
  split.
  { unfold zx16, TW.s32_at. rewrite (unsigned_lit _ (cia_r16 _ HRT)). rewrite <- RTY.
    rewrite (Z.mod_small _ _ HRT). rewrite (cia_swrap32 _ (cia_r16s _ HRT)). reflexivity. }
  split.
  { unfold TW.put, le4. rewrite (unsigned_lit _ (cia_r32 _ RC)). reflexivity. }
  unfold TW.put, le2. rewrite (unsigned_lit _ (cia_r16 _ HRT)). reflexivity.
Qed.

(* The post from the walk's facts: Bw' = Bw, and the world after the run (the frame is outside the hull). *)
Lemma cia_post :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Bw : list byte),
    tw_at TMAP_B (csw_view m) Bw ->
    off_stk sp 16 TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO) ->
    forall ms', (exists (a0' a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp)) ->
    exists (a0' a1' a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         Bw = Bw /\
         tw_at TMAP_B (csw_view m') Bw.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Bw HW HOFF ms'
    (a0' & a1' & a2' & a3' & a4' & a5' & m' & E & MU & WM & ST').
  exists a0', a1', a2', a3', a4', a5', m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST'|]. split; [reflexivity|].
  (* The frame lies outside the hull: the off_stk premise, split by hand. Not `lia`: the kit's lia prunes every
     hypothesis that is not plain arithmetic (no case for `or`). *)
  apply (cia_kept m m' _ _ Bw HW MU). unfold off_stk in HOFF.
  destruct HOFF as [HOFF|HOFF]; [right | left]; exact HOFF.
Qed.


Theorem check_inflight_acked_holds_F : check_inflight_acked_contract_F.
Proof.
  unfold check_inflight_acked_contract_F, CHECK_INFLIGHT_ACKED, CHECK_INFLIGHT_ACKED_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p lo n Bw Bw' HP0 HP8 HRT B64 B68 HW HM ST HLO HOFF CELLS APW1 APW2 DGOT DCELL D64 A64 D68 A68
    RFR RGA ROA RGOT RCELL RS64 RF64 ROC RS68 RF68 ROR.
  (* the model *)
  destruct (cia_model Bw n Bw' HM) as (M1 & CTR & RTY & ->). clear HM.
  rewrite <- cia_got, <- cia_ow in M1.
  destruct (cia_vals Bw n CTR RTY HRT) as (RC & EQC & EQR & P4 & P2). clear CTR RTY.
  rewrite P4 in B64. rewrite P2 in B68. clear P4 P2.
  (* the four world loads, as raw memory *)
  rewrite check_inflight_acked_got_acked_at in RGA.
  rewrite check_inflight_acked_ow_acked_at in ROA.
  rewrite check_inflight_acked_ow_counter_at in ROC.
  rewrite check_inflight_acked_ow_retry_at in ROR.
  destruct (cia_world m Bw HW) as ((BGA & LGA) & (BOA & LOA) & (BOC & LOC) & (BOR & LOR)).
  (* the walk, and the post *)
  exact (cia_walk RNG _ ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p lo (TI.n_counter n) (TI.n_retry n)
    (TW.s32_at Bw 65300) (TW.s32_at Bw 65528) (TW.s32_at Bw 65536) (TW.s32_at Bw 65540)
    (TW.sub Bw 65300 4) (TW.sub Bw 65528 4) (TW.sub Bw 65536 4) (TW.sub Bw 65540 4)
    HP0 HP8 RC HRT B64 B68 BGA LGA BOA LOA BOC LOC BOR LOR
    (lw_world Bw 65300) (lw_world Bw 65528) (lw_world Bw 65536) (lw_world Bw 65540)
    (TWorldLemmas.s32_range Bw 65300) (TWorldLemmas.s32_range Bw 65528) M1 EQC EQR
    ST HLO HOFF CELLS APW1 APW2 DGOT DCELL D64 A64 D68 A68
    RFR RGA ROA RGOT RCELL RS64 RF64 ROC RS68 RF68 ROR
    (cia_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Bw HW HOFF)).
Qed.

Print Assumptions check_inflight_acked_holds_F.
