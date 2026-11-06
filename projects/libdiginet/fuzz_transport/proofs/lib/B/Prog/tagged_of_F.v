From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_wake_c tagged_of_c tagged_of_F_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Proof of tagged_of_contract_F (image B, entry 0x846a0, 236 bytes, frame 16 bytes), with StepF's step: each access
   side goal is closed from the rng fact of the range it touches. The functional steps are the UBSan walk's
   (lib/U/Prog/T/tagged_of.v); image B adds the frame, the three instrumented checks and the unimp word.

   The walk (listing DgnTransportBList.v, the 59 slots from AF_tagged_of = 0x3400):
     0x846a0-0x846a4  addi sp,sp,-16; sd ra,8(sp): the frame, carved from stk.
     0x846a8-0x846ac  li a2,3; bltu a1,a2 to 0x84750: n < 3 returns NULL.
     0x846b0          beqz a0 to 0x84760 (the unimp word): ruled out by 0 < b.
     0x846b4-0x846bc  a1 = the 8 bytes at GOT_CELL_K = 0xa3cf0, then a2 = the 8 bytes at CELL_K = 0xac678:
                      0x7fff8000 (asan_cells).
     0x846c0-0x846cc  the shadow byte k0 of b (srli, add, lb); bnez to 0x84764: andi a3,a0,7; blt a3,a1 back to
                      0x846d0, else 0x8476c calls __asan_report_load1.
     0x846d0-0x846d8  a1 = l[0]; li a3,160; bne a1,a3 to 0x84750: l[0] <> TAG returns NULL.
     0x846dc-0x846e4  a1 = b + 2; li a3,1; bgeu a3,a1 to the unimp word: b + 2 does not wrap (addressable).
     0x846e8-0x846f8  a0 = b + 1; the shadow byte k1 of b + 1; bnez to 0x84770: andi a4,a0,7; blt a4,a3 back to
                      0x846fc, else 0x84778 calls __asan_report_load1.
     0x846fc-0x8470c  the shadow byte k2 of b + 2 (in a2); a0 = l[1]; bnez a2 to 0x8477c: andi a3,a1,7; blt a3,a2
                      back to 0x84710, else 0x84788 calls __asan_report_load1.
     0x84710-0x84720  a1 = l[2]; a2 = the 4-byte load of g_ncmd at 0x5df600, sign-extended; a0 = serial =
                      (l[2] << 7) | l[1].
     0x84724          bgeu a0,a2 to 0x84750: serial >= g_ncmd returns NULL.
     0x84728-0x8472c  li a1,0x401; bgeu a0,a1 to the unimp word: ruled out by serial < CMDS_MAX (the model).
     0x84730-0x84744  a0 = 40 serial; a1 = g_cmd; bltu (not a1),a0 to the unimp word: g_cmd + 40 serial does not wrap.
     0x84748-0x8474c  a0 = g_cmd + 40 serial; j 0x84754.
     0x84750          li a0,0.
     0x84754-0x8475c  ld ra,8(sp); addi sp,sp,16; ret: the one return.
   The paths the premises rule out:
     - __asan_report_load1 (0x8476c, 0x84778, 0x84788): addressable m b 3 gives, for the byte b + j, a shadow byte k
       with k = 0 or (b + j) mod 8 < k (tgo_addr3), so each check falls through or its blt goes back;
     - the unimp word 0x84760: b = 0 by 0 < b; b + 2 <= 1 (unsigned) by b + 3 <= APPMEM_END; serial >= 0x401 and
       g_cmd + 40 serial >= 2^64 by serial < 1024, which tagged_of_m Bw l n = Some _ gives on the path that reaches
       them (serial < g_ncmd).
   Each instrumented check either falls through or takes its two-word handler back to the next word with one more
   register written; the walk proves the run from that next word once, for any value of that register (CK0, CK1,
   CK2), and the one return once, for any a0 .. a4 with a0 = tagged_of_res t (RET).
   The world after: the run writes only its frame (munch), and the frame lies outside the hull
   [G_HARNESS_B_LO, G_HARNESS_B_HI) of the 18 payload ranges (the off_stk premise), so tw_at holds of the same Bw
   (tgo_kept), and the model premise gives Bw' = Bw. *)

(* ---- the model: Bw' = Bw, and the result on each path of the code (TCb.v tagged_of_m) ---- *)

Lemma tgo_some : forall (B B' : list byte) (x t : option Z), Some (B, x) = Some (B', t) -> B' = B /\ t = x.
Proof.
  intros B B' x t H.
  pose proof (f_equal (fun o : option (list byte * option Z) => match o with Some (p, _) => p | None => B end) H)
    as E1.
  pose proof (f_equal (fun o : option (list byte * option Z) => match o with Some (_, q) => q | None => x end) H)
    as E2.
  cbv beta iota in E1, E2. split; symmetry; [exact E1 | exact E2].
Qed.

Lemma tgo_m : forall Bw l n Bw' t, TC.tagged_of_m Bw l n = Some (Bw', t) ->
  Bw' = Bw /\
  (n < 3 -> t = None) /\
  (3 <= n -> exists b0 r, l = b0 :: r /\
     (bv_unsigned b0 <> 160 -> t = None) /\
     (bv_unsigned b0 = 160 -> exists b1 b2 r', r = b1 :: b2 :: r' /\
        (TW.g_ncmd Bw <= Z.lor (Z.shiftl (bv_unsigned b2) 7) (bv_unsigned b1) -> t = None) /\
        (Z.lor (Z.shiftl (bv_unsigned b2) 7) (bv_unsigned b1) < TW.g_ncmd Bw ->
           Z.lor (Z.shiftl (bv_unsigned b2) 7) (bv_unsigned b1) < 1024 /\
           t = Some (Z.lor (Z.shiftl (bv_unsigned b2) 7) (bv_unsigned b1))))).
Proof.
  intros Bw l n Bw' t H. unfold TC.tagged_of_m in H.
  destruct (Z_lt_le_dec n 3) as [N|N].
  { rewrite (proj2 (Z.ltb_lt n 3) N) in H. apply tgo_some in H as [-> ->].
    split; [reflexivity|]. split; [intros _; reflexivity | intros X; exfalso; lia]. }
  rewrite (proj2 (Z.ltb_ge n 3) N) in H.
  destruct l as [|b0 r]; [cbn [length Nat.ltb Nat.leb] in H; discriminate H|].
  cbn [length Nat.ltb Nat.leb] in H.
  match type of H with context [Z.eqb ?A TC.TAG] => replace A with (bv_unsigned b0) in H by reflexivity end.
  destruct (Z.eq_dec (bv_unsigned b0) 160) as [T|T].
  2: { rewrite (proj2 (Z.eqb_neq (bv_unsigned b0) TC.TAG) T) in H. cbn [negb] in H.
       apply tgo_some in H as [-> ->].
       split; [reflexivity|]. split; [intros X; exfalso; lia|]. intros _. exists b0, r.
       split; [reflexivity|]. split; [intros _; reflexivity | intros X; exfalso; lia]. }
  rewrite (proj2 (Z.eqb_eq (bv_unsigned b0) TC.TAG) T) in H. cbn [negb] in H.
  destruct r as [|b1 [|b2 r']]; [cbn [length Nat.ltb Nat.leb] in H; discriminate H
                                | cbn [length Nat.ltb Nat.leb] in H; discriminate H |].
  cbn [length Nat.ltb Nat.leb] in H. cbv zeta in H.
  match type of H with context [Z.lor ?A (Z.shiftl ?B 7)] =>
    replace A with (bv_unsigned b1) in H by reflexivity; replace B with (bv_unsigned b2) in H by reflexivity
  end.
  rewrite (Z.lor_comm (bv_unsigned b1)) in H.
  remember (Z.lor (Z.shiftl (bv_unsigned b2) 7) (bv_unsigned b1)) as s eqn:Es in H.
  assert (G : s < TW.g_ncmd Bw -> s < 1024 /\ Bw' = Bw /\ t = Some s).
  { intros G. rewrite (proj2 (Z.ltb_lt _ _) G) in H. cbv iota in H.
    destruct (Z_lt_le_dec s TC.CMDS_MAX) as [C|C].
    - rewrite (proj2 (Z.leb_gt _ _) C) in H. cbv iota in H. apply tgo_some in H as [E1 E2].
      unfold TC.CMDS_MAX in C. split; [exact C|]. split; [exact E1 | exact E2].
    - rewrite (proj2 (Z.leb_le _ _) C) in H. cbv iota in H. discriminate H. }
  destruct (Z_lt_le_dec s (TW.g_ncmd Bw)) as [L|L].
  - destruct (G L) as (C & -> & ->). clear G.
    split; [reflexivity|]. split; [intros X; exfalso; lia|]. intros _. exists b0, (b1 :: b2 :: r').
    split; [reflexivity|]. split; [intros X; exfalso; lia|]. intros _. exists b1, b2, r'. rewrite <- Es.
    split; [reflexivity|]. split; [intros X; exfalso; lia|]. intros _. split; [exact C | reflexivity].
  - clear G. rewrite (proj2 (Z.ltb_ge _ _) L) in H. cbv iota in H. apply tgo_some in H as [-> ->].
    split; [reflexivity|]. split; [intros X; exfalso; lia|]. intros _. exists b0, (b1 :: b2 :: r').
    split; [reflexivity|]. split; [intros X; exfalso; lia|]. intros _. exists b1, b2, r'. rewrite <- Es.
    split; [reflexivity|]. split; [intros _; reflexivity | intros X; exfalso; lia].
Qed.

(* lw sign-extends the 32-bit g_ncmd and bgeu compares unsigned: for serial < 2^31 this is serial < g_ncmd (the
   UBSan walk's tg_ncmd_lt, at the world offset of g_ncmd) *)
Lemma tgo_ncmd_lt : forall s Bw, 0 <= s < 2 ^ 31 ->
  (s < TW.s32_at Bw 64984 mod 18446744073709551616 <-> s < TW.g_ncmd Bw).
Proof.
  intros s B Hs. unfold TW.s32_at, TW.g_ncmd, TW.OFF_g_ncmd.
  pose proof (TWorldLemmas.u_at_range B 64984 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  set (g := TW.u_at B 64984 4) in *.
  assert (E : bv_swrap 32 g = (g + 2^31) mod 2^32 - 2^31) by reflexivity.
  rewrite E.
  destruct (Z_lt_le_dec g (2^31)) as [L|L].
  - rewrite (Z.mod_small (g + 2^31) (2^32)) by lia.
    replace (g + 2^31 - 2^31) with g by lia.
    rewrite (Z.mod_small g) by lia. split; intro; lia.
  - replace (g + 2^31) with ((g - 2^31) + 1 * 2^32) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (g - 2^31) (2^32)) by lia.
    replace (g - 2^31 - 2^31) with ((g - 2^32 + 18446744073709551616) + (-1) * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. split; intro; lia.
Qed.

(* ---- the world bytes of g_ncmd, as raw memory ---- *)

Lemma tgo_ncmd_bytes : forall m Bw, tw_at TMAP_B (csw_view m) Bw ->
  bytes_at rsegs m 0x5df600 (TW.sub Bw 64984 4).
Proof.
  intros m Bw HW.
  exact (tw_bytes_at rsegs m TMAP_B Bw TW.OFF_g_ncmd TB_g_ncmd TW.SZ_g_ncmd 0 4 TMAP_B_ok HW TMAP_B_g_ncmd
    ltac:(lia) ltac:(unfold TW.SZ_g_ncmd; lia)).
Qed.

Lemma tgo_ncmd_len : forall m Bw, tw_at TMAP_B (csw_view m) Bw -> length (TW.sub Bw 64984 4) = 4%nat.
Proof.
  intros m Bw HW. apply TWorldLemmas.length_sub; [lia|].
  rewrite (tw_len TMAP_B _ Bw HW). unfold TW.W_LEN. lia.
Qed.

(* ---- memory facts over image B's rsegs ---- *)

(* the bytes of a bytes_at fact, read as the load step reads them (check_latest_frame_F.v clf_rd_all) *)
Lemma tgo_rd_all : forall m a bs n, bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H <-.
  pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r, skipn_O, firstn_all in R. exact R.
Qed.

Lemma tgo_byte0 : forall m a x0 r, bytes_at rsegs m a (x0 :: r) -> mrd rsegs m (wa a) = Some x0.
Proof.
  intros m a x0 r (_ & _ & H). pose proof (H 0%nat ltac:(cbn [length]; lia)) as E.
  change (Z.of_nat 0) with 0 in E. rewrite Z.add_0_r in E. exact E.
Qed.

Lemma tgo_byte12 : forall m a x0 x1 x2 r, bytes_at rsegs m a (x0 :: x1 :: x2 :: r) ->
  mrd rsegs m (wa (a + 1)) = Some x1 /\ mrd rsegs m (wa (a + 2)) = Some x2.
Proof.
  intros m a x0 x1 x2 r (_ & _ & H).
  pose proof (H 1%nat ltac:(cbn [length]; lia)) as E1. pose proof (H 2%nat ltac:(cbn [length]; lia)) as E2.
  change (Z.of_nat 1) with 1 in E1. change (Z.of_nat 2) with 2 in E2. split; [exact E1 | exact E2].
Qed.

(* the three bytes of addressable m b 3: each is application memory, and its shadow byte k is 0 or above its
   offset in the granule *)
Lemma tgo_addr3 : forall m b, addressable m b 3 ->
  0 <= b /\ b + 3 <= APPMEM_END /\
  forall j, 0 <= j < 3 -> app_mem (b + j) /\
    exists k, mrd rsegs m (wa ((b + j) / 8 + ASAN_K)) = Some k /\
              (bv_signed k = 0 \/ ((b + j) mod 8 < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros m b (P0 & N0 & PE & AB). split; [exact P0|]. split; [exact PE|].
  intros j Hj. destruct (AB j Hj) as (APP & k & MK & SK).
  split; [exact APP|]. exists k. split; [exact MK | exact SK].
Qed.

(* a shadow byte of an application address lies outside a 16-byte frame of application memory
   (check_latest_frame_F.v clf_shadow_tp) *)
Lemma tgo_shadow_tp : forall m m' lo hi a k, munch [(lo, hi)] m m' -> lo + 16 = hi ->
  app_mem lo -> app_mem (hi - 1) -> app_mem a ->
  mrd rsegs m (wa (a / 8 + ASAN_K)) = Some k -> mrd rsegs m' (wa (a / 8 + ASAN_K)) = Some k.
Proof.
  intros m m' lo hi a k MU E A1 A2 A3 H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2, A3. unfold ASAN_K in *.
  apply (mrd_tp m m' lo hi _ k MU); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | exact H].
Qed.

(* the shadow byte of b + j (0 <= j <= 2) lies in the footprint's shadow range of [b, b + 3) *)
Lemma tgo_rng_sh : forall RNG b x (h : word), 0 <= b -> b <= x <= b + 2 ->
  bv_unsigned h = x / 8 + 2147450880 ->
  ExecF.rng RNG (shadow_addr b) (shadow_addr (b + 2) - shadow_addr b + 1) ->
  ExecF.rng RNG (bv_unsigned h) 1.
Proof.
  intros RNG b x h Hb Hx Eh H. rewrite Eh.
  apply (rng_sub' _ _ _ _ _ H). unfold shadow_addr, ASAN_K.
  assert (D1 : b / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : x / 8 <= (b + 2) / 8) by (apply Z.div_le_mono; lia).
  lia.
Qed.

(* the shadow address of an application byte below 2^47 *)
Lemma tgo_div8 : forall x, 0 <= x < 2 ^ 47 -> 0 <= x / 8 < 2 ^ 44.
Proof. intros x H. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

(* lib/A/Prog/TWorldAKept.v csw_kept over image B: a run that writes only [lo, hi), outside the hull of the 18
   harness globals, keeps tw_at at the leaf form's view csw_view with the same world (TWorldB.v TMAP_B_kept) *)
Lemma tgo_kept : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_B (csw_view m) Bw -> munch [(lo, hi)] m m' ->
  (hi <= TG.G_HARNESS_B_LO \/ TG.G_HARNESS_B_HI <= lo) ->
  tw_at TMAP_B (csw_view m') Bw.
Proof. intros m m' lo hi Bw. unfold csw_view. exact (@TMAP_B_kept rsegs m m' lo hi Bw). Qed.

(* ---- the joins of the walk ---- *)

(* the run from pc, with the value v of one register left open: H holds of the goal's state at pc for any value in
   v's place *)
Local Ltac tgo_cont H v pc :=
  lazymatch goal with
  | |- ExecF.evtF ?s ?RN ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
      lazymatch eval pattern v in R with
      | ?f _ => assert (H : forall x : word, ExecF.evtF s RN Q (MS (f x) FF (Z_to_bv 64 pc) fcc rv mm ro))
      end
  end.

(* the one return 0x84754-0x8475c, with a0 .. a4 left open and a0 = tagged_of_res t *)
Local Ltac tgo_ret H v0 v1 v2 v3 v4 t :=
  lazymatch goal with
  | |- ExecF.evtF ?s ?RN ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
      lazymatch eval pattern v0, v1, v2, v3, v4 in R with
      | ?f _ _ _ _ _ =>
          assert (H : forall x0 x1 x2 x3 x4 : word, x0 = Z_to_bv 64 (tagged_of_res t) ->
                    ExecF.evtF s RN Q (MS (f x0 x1 x2 x3 x4) FF (Z_to_bv 64 0x84754) fcc rv mm ro))
      end
  end.

(* a branch the premises rule out: its condition, in Z, contradicts the facts named *)
Local Ltac tgo_no C := exfalso; zify_cond C; rewrite ?unsigned_lit_wrap in C.

Theorem tagged_of_holds_F : tagged_of_contract_F.
Proof.
  unfold tagged_of_contract_F, TAGGED_OF, TAGGED_OF_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo Bw Bw' b n l t HA0 HA1 Hn Hb HB HW HM ST HLO HOFF CELLS APW1 APW2 DGOT DCELL DB AB
    RFR RGOT RCELL RNCMD RB RSH.
  (* ---- the model: Bw' = Bw, and the result of each path (fuzz_transport.c:609-615) ---- *)
  destruct (tgo_m _ _ _ _ _ HM) as (-> & MN3 & MGE3). clear HM.
  assert (UN : bv_unsigned a1 = n) by (rewrite HA1; apply unsigned_lit; exact Hn).
  clear HA1. subst n.
  (* ---- the ranges of the stack, the cells and g_ncmd ---- *)
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  unfold off_stk, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in HOFF.
  unfold off_stk, GOT_CELL_K, CELL_K in DGOT, DCELL.
  unfold GOT_CELL_K, CELL_K in RGOT, RCELL.
  rewrite tagged_of_ncmd_at in RNCMD.
  pose proof (tgo_ncmd_bytes m Bw HW) as BN.
  pose proof (tgo_ncmd_len m Bw HW) as LN.
  (* keep the bytes_at facts off transport_chunks: they are carried past the ra store by hand *)
  pose proof (conj HB (conj CELLS (conj BN I))) as KEEP. clear HB CELLS BN.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  (* 0x846a0-0x846a4: the frame and the store of ra *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  match goal with WM' : wmono rsegs m m0 |- _ => rename WM' into WM1 end.
  destruct KEEP as (HB & CELLS & BN & _).
  destruct CELLS as (CC & CG & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CC, CG.
  assert (CG0 : bytes_at rsegs m0 0xa3cf0 (le8 (wa 0xac678))).
  { apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; destruct DGOT as [D|D]; [left|right]; lia | exact CG]. }
  assert (CC0 : bytes_at rsegs m0 0xac678 (le8 (wa 0x7fff8000))).
  { apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite length_le8; destruct DCELL as [D|D]; [left|right]; lia | exact CC]. }
  assert (BN0 : bytes_at rsegs m0 0x5df600 (TW.sub Bw 64984 4)).
  { apply (bytes_tp m m0 _ _ _ _ MU1); [rewrite LN; destruct HOFF as [D|D]; [left|right]; lia | exact BN]. }
  pose proof (tgo_rd_all m0 _ _ 8 CG0 (length_le8 _)) as RDG.
  pose proof (tgo_rd_all m0 _ _ 8 CC0 (length_le8 _)) as RDS.
  pose proof (tgo_rd_all m0 _ _ 4 BN0 LN) as RDN.
  clear CC CG BN CG0 CC0 BN0.
  (* ---- the one return (0x84754-0x8475c), for any a0 .. a4 with a0 = tagged_of_res t ---- *)
  tgo_ret RET a0 a1 a2 a3 a4 t.
  { intros x0 x1 x2 x3 x4 E0. cbv beta. subst x0.
    step. step. step.
    apply evtF_done. do 5 eexists. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|].
    split; [release_frame FR ST (bv_unsigned sp); exact ST|].
    split; [reflexivity|].
    apply (tgo_kept m m0 _ _ Bw HW MU1).
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI.
    destruct HOFF as [D|D]; [right | left]; clear - D; lia. }
  (* 0x846a8-0x846ac: li a2,3; bltu a1,a2: n < 3 returns NULL (0x84750: li a0,0) *)
  step. step.
  destruct (Z_lt_le_dec (bv_unsigned a1) 3) as [N3|N3].
  { if_cases Hbr1; [| tgo_no Hbr1; clear - Hbr1 N3 Hn; Z.div_mod_to_equations; lia].
    step. apply RET. rewrite (MN3 N3). reflexivity. }
  if_cases Hbr1; [tgo_no Hbr1; clear - Hbr1 N3 Hn; Z.div_mod_to_equations; lia |].
  clear MN3.
  (* ---- 3 <= n: the code reads b; the model gives l a first byte ---- *)
  destruct (MGE3 N3) as (b0 & r & -> & MT0 & MTAG). clear MGE3.
  specialize (DB N3). specialize (AB N3). specialize (RB N3). specialize (RSH N3).
  destruct (tgo_addr3 m b AB) as (P0 & E3 & AJ). clear AB.
  unfold APPMEM_END in E3.
  assert (U0 : bv_unsigned a0 = b) by (rewrite HA0; apply unsigned_lit; lia).
  clear HA0. subst b.
  unfold off_stk in DB.
  destruct (AJ 0 ltac:(lia)) as (APP0 & k0 & MS0 & SK0).
  destruct (AJ 1 ltac:(lia)) as (APP1 & k1 & MS1 & SK1).
  destruct (AJ 2 ltac:(lia)) as (APP2 & k2 & MS2 & SK2).
  clear AJ. rewrite Z.add_0_r in APP0, MS0, SK0.
  apply (tgo_shadow_tp m m0 _ _ _ _ MU1 ltac:(lia) APW1 APW2 APP0) in MS0.
  apply (tgo_shadow_tp m m0 _ _ _ _ MU1 ltac:(lia) APW1 APW2 APP1) in MS1.
  apply (tgo_shadow_tp m m0 _ _ _ _ MU1 ltac:(lia) APW1 APW2 APP2) in MS2.
  unfold ASAN_K in MS0, MS1, MS2.
  pose proof (tgo_byte0 m _ _ _ HB) as M0.
  assert (M0' : mrd rsegs m0 (wa (bv_unsigned a0)) = Some b0)
    by (apply (mrd_tp m m0 _ _ _ _ MU1); [lia | destruct DB as [D|D]; [left|right]; lia | exact M0]).
  clear M0.
  (* 0x846b0: beqz a0 to the unimp word; 0 < b *)
  step. if_cases Hbr2; [tgo_no Hbr2; clear - Hbr2 Hb; Z.div_mod_to_equations; lia |].
  (* 0x846b4-0x846bc: a1 = the GOT cell, a2 = 0x7fff8000 *)
  step. step. step. clear RDG RDS.
  (* 0x846c0-0x846c8: the shadow byte of b, k0 *)
  step. gen_shr a0 g0 G0.
  pose proof (tgo_div8 (bv_unsigned a0) ltac:(lia)) as D0.
  step. gen_addi g0 h0 H0.
  pose proof (tgo_rng_sh RNG (bv_unsigned a0) (bv_unsigned a0) h0 ltac:(lia) ltac:(lia) ltac:(lia) RSH) as RH0.
  pose proof (rdw0 m0 h0 _ _ MS0 ltac:(lia)) as R. step. clear R.
  (* 0x846cc: bnez a1; the handler 0x84764-0x84768 goes back to 0x846d0 *)
  step.
  tgo_cont CK0 a3 0x846d0.
  2: { cbv beta in CK0. destruct SK0 as [S0|[S0 S0u]].
       - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) S0); cbn [negb]. apply CK0.
       - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k0) 0) ltac:(lia)); cbn [negb].
         step. step.
         pose proof (Z.mod_pos_bound (bv_unsigned a0) 8 ltac:(lia)) as MB0.
         rewrite land7, (lts_low (bv_unsigned a0 mod 8) k0 ltac:(lia)), (proj2 (Z.ltb_lt _ _) S0); cbn [negb].
         apply CK0. }
  intros x3. cbv beta.
  (* 0x846d0-0x846d8: a1 = l[0]; li a3,160; bne a1,a3: l[0] <> TAG returns NULL *)
  pose proof (rdw0 m0 a0 _ _ M0' eq_refl) as R. step. clear R.
  step. step.
  pose proof (byte_range b0) as UB0.
  destruct (Z.eq_dec (bv_unsigned b0) 160) as [T0|T0].
  2: { if_cases Hbr3; [| tgo_no Hbr3; clear - Hbr3 T0 UB0; Z.div_mod_to_equations; lia].
       step. apply RET. rewrite (MT0 T0). reflexivity. }
  if_cases Hbr3; [tgo_no Hbr3; clear - Hbr3 T0 UB0; Z.div_mod_to_equations; lia |].
  clear MT0.
  (* l[0] = TAG: the model gives l three bytes *)
  destruct (MTAG T0) as (b1 & b2 & r' & -> & MG1 & MG2). clear MTAG.
  pose proof (byte_range b1) as UB1. pose proof (byte_range b2) as UB2.
  destruct (tgo_byte12 m _ _ _ _ _ HB) as (M1 & M2).
  assert (M1' : mrd rsegs m0 (wa (bv_unsigned a0 + 1)) = Some b1)
    by (apply (mrd_tp m m0 _ _ _ _ MU1); [lia | destruct DB as [D|D]; [left|right]; lia | exact M1]).
  assert (M2' : mrd rsegs m0 (wa (bv_unsigned a0 + 2)) = Some b2)
    by (apply (mrd_tp m m0 _ _ _ _ MU1); [lia | destruct DB as [D|D]; [left|right]; lia | exact M2]).
  clear M1 M2.
  (* 0x846dc-0x846e4: a1 = b + 2; li a3,1; bgeu a3,a1 to the unimp word: b + 2 does not wrap *)
  step. gen_addi a0 w2 U2.
  step. step.
  if_cases Hbr4; [tgo_no Hbr4; clear - Hbr4 U2 Hb; Z.div_mod_to_equations; lia |].
  (* 0x846e8-0x846f4: a0 = b + 1; the shadow byte of b + 1, k1 *)
  step. gen_addi a0 w1 U1.
  step. gen_shr w1 g1 G1. rewrite U1 in G1.
  pose proof (tgo_div8 (bv_unsigned a0 + 1) ltac:(lia)) as D1.
  step. gen_addi g1 h1 H1.
  pose proof (tgo_rng_sh RNG (bv_unsigned a0) (bv_unsigned a0 + 1) h1 ltac:(lia) ltac:(lia) ltac:(lia) RSH) as RH1.
  pose proof (rdw0 m0 h1 _ _ MS1 ltac:(lia)) as R. step. clear R.
  (* 0x846f8: bnez a3; the handler 0x84770-0x84774 goes back to 0x846fc *)
  step.
  tgo_cont CK1 a4 0x846fc.
  2: { cbv beta in CK1. destruct SK1 as [S1|[S1 S1u]].
       - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) S1); cbn [negb]. apply CK1.
       - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k1) 0) ltac:(lia)); cbn [negb].
         step. step.
         pose proof (Z.mod_pos_bound (bv_unsigned a0 + 1) 8 ltac:(lia)) as MB1.
         rewrite land7, U1, (lts_low ((bv_unsigned a0 + 1) mod 8) k1 ltac:(lia)), (proj2 (Z.ltb_lt _ _) S1);
           cbn [negb].
         apply CK1. }
  intros x4. cbv beta.
  (* 0x846fc-0x84708: the shadow byte of b + 2, k2 (in a2); a0 = l[1] *)
  step. gen_shr w2 g2 G2. rewrite U2 in G2.
  pose proof (tgo_div8 (bv_unsigned a0 + 2) ltac:(lia)) as D2.
  step. gen_addi g2 h2 H2.
  pose proof (tgo_rng_sh RNG (bv_unsigned a0) (bv_unsigned a0 + 2) h2 ltac:(lia) ltac:(lia) ltac:(lia) RSH) as RH2.
  pose proof (rdw0 m0 h2 _ _ MS2 ltac:(lia)) as R. step. clear R.
  pose proof (rng_sub' _ _ _ (bv_unsigned w1) 1 RB ltac:(lia)) as RW1.
  pose proof (rdw0 m0 w1 _ _ M1' U1) as R. step. clear R.
  (* 0x8470c: bnez a2; the handler 0x8477c-0x84780 goes back to 0x84710 *)
  step.
  tgo_cont CK2 g2 0x84710.
  2: { cbv beta in CK2. destruct SK2 as [S2|[S2 S2u]].
       - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) S2); cbn [negb]. apply CK2.
       - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k2) 0) ltac:(lia)); cbn [negb].
         step. step.
         pose proof (Z.mod_pos_bound (bv_unsigned a0 + 2) 8 ltac:(lia)) as MB2.
         rewrite land7, U2, (lts_low ((bv_unsigned a0 + 2) mod 8) k2 ltac:(lia)), (proj2 (Z.ltb_lt _ _) S2);
           cbn [negb].
         apply CK2. }
  intros x5. cbv beta.
  (* 0x84710: a1 = l[2] *)
  pose proof (rng_sub' _ _ _ (bv_unsigned w2) 1 RB ltac:(lia)) as RW2.
  pose proof (rdw0 m0 w2 _ _ M2' U2) as R. step. clear R.
  (* 0x84714-0x84718: a2 = g_ncmd, sign-extended *)
  step. step. rewrite lw_world. clear RDN.
  (* 0x8471c-0x84720: a0 = serial = (l[2] << 7) | l[1] *)
  step. step.
  unfold zxb.
  rewrite ?(unsigned_lit (bv_unsigned b2)) by lia.
  rewrite ?(unsigned_lit (bv_unsigned b1)) by lia.
  rewrite ?(unsigned_lit (Z.shiftl (bv_unsigned b2) 7)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (lor_lt_pow2 (Z.shiftl (bv_unsigned b2) 7) (bv_unsigned b1) 15
    ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia) ltac:(lia)) as SR.
  set (ser := Z.lor (Z.shiftl (bv_unsigned b2) 7) (bv_unsigned b1)) in *.
  clearbody ser.
  (* 0x84724: bgeu a0,a2: serial >= g_ncmd returns NULL *)
  step.
  pose proof (tgo_ncmd_lt ser Bw ltac:(lia)) as NL.
  destruct (Z_lt_le_dec ser (TW.g_ncmd Bw)) as [GN|GN].
  2: { assert (NL' : ~ ser < TW.s32_at Bw 64984 mod 18446744073709551616)
         by (intros X; apply NL in X; lia).
       if_cases Hbr5; [| tgo_no Hbr5; clear - Hbr5 NL' SR; Z.div_mod_to_equations; lia].
       step. apply RET. rewrite (MG1 GN). reflexivity. }
  pose proof (proj2 NL GN) as GN'.
  if_cases Hbr5; [tgo_no Hbr5; clear - Hbr5 GN' SR; Z.div_mod_to_equations; lia |].
  destruct (MG2 GN) as (CM & Et). clear MG1 MG2.
  (* 0x84728-0x8472c: li a1,0x401; bgeu a0,a1 to the unimp word: serial < 1024 *)
  step. step.
  if_cases Hbr6; [tgo_no Hbr6; clear - Hbr6 CM SR; Z.div_mod_to_equations; lia |].
  (* 0x84730-0x84744: a0 = 40 serial; a1 = g_cmd; a2 = not a1; bltu a2,a0 to the unimp word: no wrap *)
  step. step. step. step. step.
  step.
  if_cases Hbr7; [tgo_no Hbr7; clear - Hbr7 CM SR; Z.div_mod_to_equations; lia |].
  (* 0x84748-0x8474c: a0 = g_cmd + 40 serial; j 0x84754 *)
  step. step.
  apply RET. rewrite Et. cbn [tagged_of_res]. unfold TB_g_cmd.
  apply Z_to_bv_eqm. rewrite ?unsigned_lit_wrap. clear - SR CM. Z.div_mod_to_equations. lia.
Qed.

Print Assumptions tagged_of_holds_F.
