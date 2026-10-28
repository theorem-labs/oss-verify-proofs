(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface RtB_Annot BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BecLazy.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts StrLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_MILB LbB_Own LbB_ContStmt LbB_ContV4R LbB_ContV4 LbB_ContVotR LbB_ContVot LbB_SegKit LbB_StrPbR LbB_StrPb LbB_MkStrR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition MKSTR_STACK : Z := 80 + SPB_STACK.

Definition wchars (x : Z) : list Z := word_chars (x mod 2 ^ 32) 4.

Definition ms_pref (ws : list Z) (k : nat) : list Z := flat_map wchars (firstn k ws).

Lemma wchars_val : forall x, 0 <= x < 2 ^ 32 ->
  wchars x = [x mod 256; (x / 256) mod 256; (x / 256 / 256) mod 256; (x / 256 / 256 / 256) mod 256].
Proof. intros x Hx. unfold wchars. rewrite (Z.mod_small x) by lia. reflexivity. Qed.

Lemma ms_chars_cons_val : forall x ws', 0 <= x < 2 ^ 32 ->
  ms_chars (x :: ws') =
    if x mod 256 =? 0 then []
    else if (x / 256) mod 256 =? 0 then [x mod 256]
    else if (x / 256 / 256) mod 256 =? 0 then [x mod 256; (x / 256) mod 256]
    else if (x / 256 / 256 / 256) mod 256 =? 0 then [x mod 256; (x / 256) mod 256; (x / 256 / 256) mod 256]
    else wchars x ++ ms_chars ws'.
Proof.
  intros x ws' Hx. cbn [ms_chars]. fold (wchars x). rewrite (wchars_val x Hx). cbn [take_nz].
  destruct (x mod 256 =? 0); [reflexivity|].
  destruct ((x / 256) mod 256 =? 0); [reflexivity|].
  destruct ((x / 256 / 256) mod 256 =? 0); [reflexivity|].
  destruct ((x / 256 / 256 / 256) mod 256 =? 0); reflexivity.
Qed.

Definition ms_nz (ws : list Z) (k : nat) : Prop :=
  forall i, (i < k)%nat -> forall c, In c (wchars (nth i ws 0)) -> c <> 0.

Lemma ms_chars_pref : forall ws k, (k <= length ws)%nat -> (forall i, (i < length ws)%nat -> 0 <= nth i ws 0 < 2 ^ 32) ->
  ms_nz ws k -> ms_chars ws = ms_pref ws k ++ ms_chars (skipn k ws).
Proof.
  intros ws k. revert ws. induction k as [|k IH]; intros ws Hk HR HN; [reflexivity|].
  destruct ws as [|x ws']; [cbn in Hk; lia|].
  unfold ms_pref. cbn [firstn flat_map skipn]. rewrite <- app_assoc.
  assert (Hx : 0 <= x < 2 ^ 32) by exact (HR 0%nat ltac:(cbn; lia)).
  rewrite (ms_chars_cons_val x ws' Hx).
  assert (NZ : forall c, In c (wchars x) -> c <> 0) by (apply (HN 0%nat); lia).
  rewrite (wchars_val x Hx) in NZ.
  destruct (Z.eqb_spec (x mod 256) 0) as [E|E]; [exfalso; apply (NZ _ (or_introl eq_refl)) in E; exact E|].
  destruct (Z.eqb_spec ((x / 256) mod 256) 0) as [E1|E1]; [exfalso; exact (NZ _ (or_intror (or_introl eq_refl)) E1)|].
  destruct (Z.eqb_spec ((x / 256 / 256) mod 256) 0) as [E2|E2]; [exfalso; exact (NZ _ (or_intror (or_intror (or_introl eq_refl))) E2)|].
  destruct (Z.eqb_spec ((x / 256 / 256 / 256) mod 256) 0) as [E3|E3];
    [exfalso; exact (NZ _ (or_intror (or_intror (or_intror (or_introl eq_refl)))) E3)|].
  f_equal. apply IH; [cbn in Hk; lia | intros i Hi; exact (HR (S i) ltac:(cbn; lia)) |].
  intros i Hi c Hc. exact (HN (S i) ltac:(lia) c Hc).
Qed.

Lemma firstn_S_snoc : forall (ws : list Z) k, (k < length ws)%nat -> firstn (S k) ws = firstn k ws ++ [nth k ws 0].
Proof.
  induction ws as [|x ws IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. cbn in Hk. lia.
Qed.

Lemma ms_pref_S : forall ws k, (k < length ws)%nat -> ms_pref ws (S k) = ms_pref ws k ++ wchars (nth k ws 0).
Proof.
  intros ws k Hk. unfold ms_pref. rewrite (firstn_S_snoc ws k Hk). rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r. reflexivity.
Qed.

Lemma skipn_nth_cons' : forall (ws : list Z) k, (k < length ws)%nat -> skipn k ws = nth k ws 0 :: skipn (S k) ws.
Proof.
  induction ws as [|x ws IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.

Section MKS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition ms_cost (nw : Z) : Z := as_Cm H (16 * nw + 96) + as_Cf H (8 * nw + 48).

  Definition ms_phi (sb : sbuf) : Z := match sb with SShort => 0 | SLong _ asz => if 64512 <? asz then 8 * asz else 0 end.

  Definition ms_words_keep (LB : list block) (spz p : Z) (m : mem) (w nw : Z) (ws : list Z) : Prop :=
    forall m', ACONST m' -> mem_inv asegs m' -> xpres H LB spz [(p, p + 24)] m m' ->
      (forall i, 0 <= i < nw -> fldA m' (w + 4 * i) 4 (Znth i ws)) /\ accessible m' w (4 * nw).

  Definition mkstr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (p nw : Z) (ws : list Z) (lo B shi : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block)
                     (sb : sbuf) (pid : bptr),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) [(p, p + 24)] m m'
      /\ as_RHEAP H s' LB' m' /\ strA LB' m' p sb (ms_chars ws) /\ spb_blk LB' m' sb pid
      /\ (match sb with
          | SShort => LB' = LB
          | SLong d asz => LB' = (pid, d, asz) :: LB /\ ~ In pid (map blk_id LB) /\ ablock_range H d asz
                           /\ (asz = 48 \/ asz <= 2 * Zlen (ms_chars ws)) /\ Zlen (ms_chars ws) <= 4 * nw

          end)
      /\ addressable m' p 24 /\ wr_at asegs m' p 24 /\ lb_own LB' m'
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - ms_phi sb.

  Definition mkstr_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (p w : Z) (ws : list Z) (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 MKSTR_ENTRY) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 w -> a2 = Z_to_bv 64 (Zlen ws) ->
      Zlen ws < 2 ^ 24   -> (forall i, 0 <= i < Zlen ws -> 0 <= Znth i ws < 2 ^ 32) ->
      w mod 4 = 0 -> 0 <= w -> w + 4 * Zlen ws <= 2 ^ 47 ->
      ms_words_keep LB (bv_unsigned sp) p m w (Zlen ws) ws ->
      p mod 8 = 0 -> addressable m p 24 -> spb_in_ff LF p 24 -> obj_win H LB LF (bv_unsigned sp) lo p 24 ->
      ((0x6e8000 <= p /\ p + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= p /\ p + 24 <= 2 ^ 47)) ->
      wr_at asegs m p 24 -> lb_own LB m ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_small LB + 3 * 64512 <= RT_SMALL_MAX   -> Z.of_nat (length LB) + 2 <= RT_CNT_MAX ->
      nlarge LB + 2 <= RT_LARGE_MAX -> ms_cost (Zlen ws) <= as_AL H s ->
      trace_ok (as_TR H) APC0_FREE [SPB_DEL_RA] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - MKSTR_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      ACONST m -> as_RFS H LF m ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_SR H (mkstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF p (Zlen ws) ws lo B shi m mo)
        (mkCfg msF mo).
End MKS.

Lemma xpres_drop_fresh {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H ->
  forall LB SP X m1 m2 sk mk pid d asz,
    as_RHEAP H sk ((pid, d, asz) :: LB) mk -> ~ In pid (map blk_id LB) -> aceil <= SP ->
    xpres H LB SP (X ++ [(d, d + asz); (sh d, sh d + nsh asz)]) m1 m2 -> xpres H LB SP X m1 m2.
Proof.
  intros H HH LB SP X m1 m2 sk mk pid d asz RH NI HSP XP a Ha [Hc Hx].
  apply XP; [exact Ha|]. split; [exact Hc|].
  intros K. apply rin_ivs_app in K. destruct K as [K|K]; [exact (Hx K)|].
  destruct (sk_cls H HH sk LB pid d asz SP mk a RH NI HSP Hc) as [C|(C1 & C2 & C3)].
  - pose proof (ah_blocks H HH _ _ _ (pid, d, asz) RH (or_introl eq_refl)) as (R0 & _ & Rn & _ & RC & _). cbn in RC.
    pose proof (sh_below_aceil d) as SB.
    cbn [rin_ivs fst snd] in K. destruct K as [K|[K|K]]; [lia | | contradiction].
    assert (sh d + nsh asz <= sh aceil).
    { unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
    assert (sh aceil < aceil) by (apply sh_below_aceil; acb; unfold AAPP_HI; lia). lia.
  - cbn [rin_ivs fst snd] in K. destruct K as [K|[K|K]]; [exact (C2 K) | exact (C3 K) | contradiction].
Qed.

Lemma ms_shk_word : forall M c n a, accessible M c n -> c <= a -> a + 4 <= c + n -> a mod 4 = 0 ->
  exists k, LbB_Kit.shk M a k /\ (k = 0 \/ a mod 8 + 4 <= k < 8).
Proof.
  intros M c n a (A0 & A1 & AC) H1 H2 H4.
  destruct (AC (a + 3) ltac:(lia)) as (v & Hv & Hrd & Hok).
  assert (E : (a + 3) / 8 = a / 8) by (clear - H4 A0 H1; Z.div_mod_to_equations; lia).
  replace (sh (a + 3)) with (sh a) in Hrd by (unfold sh; rewrite E; reflexivity).
  pose proof (shk_of_mrd M a (b8 v) ltac:(lia) Hrd) as K. unfold b8 in K. rewrite Z_to_bv_unsigned in K.
  rewrite bv_wrap_small in K by (change (bv_modulus 8) with 256; lia).
  exists v. split; [exact K|].
  unfold byte_ok in Hok. destruct Hok as [Hv0|Hv1]; [left; exact Hv0|right].
  assert (M8 : (a + 3) mod 8 = a mod 8 + 3) by (clear - H4 A0 H1; Z.div_mod_to_equations; lia). lia.
Qed.

Lemma ms_mdef_of_wr_at : forall m a n, wr_at asegs m a n -> 0x6e8000 <= a -> CRep.mdef m a n.
Proof.
  intros m a n (W0 & W1 & W) Ha i Hi. specialize (W i Hi). unfold wview in W.
  unfold wa in W. rewrite HLib.u64_of_Z in W by lia.
  destruct (m (Z_to_bv 64 (a + i))) eqn:E; [discriminate|].
  rewrite BecLazy.asegs_find_segment_none_high in W by lia. congruence.
Qed.

Lemma ms_wr_at_rw_cells : forall m a n, wr_at asegs m a n -> 0x6e8000 <= a -> 0 <= n ->
  exists bs, rw_cells asegs m a [CB (Z.to_nat n) bs].
Proof.
  intros m a n W Ha Hn. pose proof (ms_mdef_of_wr_at m a n W Ha) as MD.
  assert (EX : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\ bytes_at asegs m a bs).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; destruct W as (_ & W1 & _); lia|]. intros i Hi. cbn in Hi. lia.
    - destruct (IH ltac:(lia)) as (bs & Lb & Bb).
      specialize (MD (Z.of_nat k) ltac:(lia)). destruct (m (Z_to_bv 64 (a + Z.of_nat k))) as [b|] eqn:E; [|congruence].
      exists (bs ++ [b]). rewrite length_app, Lb. cbn [length]. split; [lia|]. apply bytes_at_app. split; [exact Bb|].
      destruct W as (W0 & W1 & _). split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i as [|i]; [|lia].
      cbn. unfold mrd, wa. rewrite Lb, Z.add_0_r, E. reflexivity. }
  destruct (EX (Z.to_nat n) ltac:(lia)) as (bs & Lb & Bb). exists bs.
  split; [split; [cbn; split; [exact Lb | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Bb]|].
  cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
Qed.

Lemma ms_wr_at_wmono : forall m m' a n, wr_at asegs m a n -> wmono asegs m m' -> wr_at asegs m' a n.
Proof. intros m m' a n (W1 & W2 & W) WM. split; [lia|]. split; [lia|]. intros i Hi. apply WM. apply W. exact Hi. Qed.

Lemma ms_skipn_repeat : forall (A : Type) (x : A) (n k : nat), skipn k (repeat x n) = repeat x (n - k).
Proof. intros A x n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

Lemma ms_fld0 : forall m a (i : nat), bytes_at asegs m a (poison_bytes 24 0) -> (i < 24)%nat -> fldA m (a + Z.of_nat i) 1 0.
Proof.
  intros m a i HB Hi. unfold fldA, fld.
  pose proof (bytes_at_rdn asegs m a (poison_bytes 24 0) i 1 HB ltac:(unfold poison_bytes; rewrite repeat_length; lia)) as R.
  unfold wa in R. replace (word_to_le_bytes 1 (Z_to_bv 64 0)) with (firstn 1 (skipn i (poison_bytes 24 0))); [exact R|].
  unfold poison_bytes. rewrite ms_skipn_repeat.
  replace (24 - i)%nat with (S (23 - i)) by lia. cbn [repeat firstn]. vm_compute. reflexivity.
Qed.

Lemma ms_fld_hd : forall m a x b0, m (Z_to_bv 64 a) = Some b0 -> fldA m a 4 x ->
  exists r, word_to_le_bytes 4 (Z_to_bv 64 x) = b0 :: r.
Proof.
  intros m a x b0 M F. revert F. unfold fldA, fld. cbn [PropExec.rdn]. rewrite M. cbv beta iota.
  lazymatch goal with |- (match ?Y with Some _ => _ | None => _ end) = _ -> _ => destruct Y as [r|] end;
    cbv beta iota; [|intros Hc; discriminate Hc].
  intros R. exists r. congruence.
Qed.

Section MKP.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
            (p w : Z) (ws : list Z) (lo B shi spz : Z).
  Hypothesis SPZ : bv_unsigned sp = spz.
  Hypothesis SPR : 2 ^ 45 <= spz - MKSTR_STACK /\ spz <= 2 ^ 47 /\ spz mod 16 = 0.
  Hypothesis NWR : Zlen ws < 2 ^ 24.
  Hypothesis WSR : forall i, 0 <= i < Zlen ws -> 0 <= Znth i ws < 2 ^ 32.
  Hypothesis W4 : w mod 4 = 0.
  Hypothesis W0 : 0 <= w.
  Hypothesis WH : w + 4 * Zlen ws <= 2 ^ 47.
  Hypothesis WK : ms_words_keep H LB spz p m w (Zlen ws) ws.
  Hypothesis P8 : p mod 8 = 0.
  Hypothesis ADV0 : addressable m p 24.
  Hypothesis PFF : spb_in_ff LF p 24.
  Hypothesis OBJ : obj_win H LB LF spz lo p 24.
  Hypothesis PBAND : (0x6e8000 <= p /\ p + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= p /\ p + 24 <= 2 ^ 47).
  Hypothesis PWR : wr_at asegs m p 24.
  Hypothesis OWN : lb_own LB m.
  Hypothesis RH0 : as_RHEAP H s LB m.
  Hypothesis MS1 : lb_small LB + 3 * 64512 <= RT_SMALL_MAX.
  Hypothesis MS2 : Z.of_nat (length LB) + 2 <= RT_CNT_MAX.
  Hypothesis MS3 : nlarge LB + 2 <= RT_LARGE_MAX.
  Hypothesis CST : ms_cost H (Zlen ws) <= as_AL H s.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [SPB_DEL_RA].
  Hypothesis RA0 : as_rauxv_ok H m B.
  Hypothesis SPB : spz <= B.
  Hypothesis ST0 : stk asegs m lo spz.
  Hypothesis LOR : aceil <= lo /\ lo <= spz - MKSTR_STACK.
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis AC0 : ACONST m.
  Hypothesis RF0 : as_RFS H LF m.
  Hypothesis S00 : stack0 m lo shi.
  Hypothesis SHI : spz <= shi.

  Let HH : asan_rt_hyps H := rt_bp_base H HHb.
  Let nw := Zlen ws.
  Let Q := mkstr_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF p nw ws lo B shi m mo.
  Let FRAME : list cell := map (fun w => C8 w) [s8; s7; s6; s5; s4; s3; s2; s1; s0; ra].

  Lemma spz_sp' : sp = Z_to_bv 64 spz.
  Proof. rewrite <- SPZ. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Lemma ms_client0 : ~ aclient_addr H LB spz 0.
  Proof.
    intros Hc. pose proof SPR as (SPL & SPH & SP16).
    unfold MKSTR_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in SPL.
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4). unfold AIMG_TOP in FS1.
    destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
    - lia.
    - unfold aimg_client in Hc. lia.
    - pose proof (ah_blocks H HH _ _ _ _ RH0 Hb) as (R0 & _). lia.
    - pose proof (ah_blocks H HH _ _ _ _ RH0 Hb) as (R0 & _).
      unfold sh in Hr. rewrite ASHADOW_BASE_val in Hr. Z.div_mod_to_equations. lia.
    - lia.
    - unfold sh in Hc. rewrite ASHADOW_BASE_val in Hc. Z.div_mod_to_equations. lia.
    - acb. unfold sh in Hc. rewrite ASHADOW_BASE_val in Hc. Z.div_mod_to_equations. lia.
  Qed.

  Lemma ms_w_nz : 0 < nw -> w <> 0.
  Proof.
    intros NP WZ.
    remember (hd (Z_to_bv 8 0) (word_to_le_bytes 4 (Z_to_bv 64 (Znth 0 ws)))) as hb eqn:Ehb.
    set (b' := Z_to_bv 8 (bv_unsigned hb + 1)).
    assert (NE : b' <> hb).
    { intros E. pose proof (f_equal bv_unsigned E) as E2. subst b'. rewrite Z_to_bv_unsigned in E2.
      rewrite bv_wrap8_mod in E2.
      pose proof (bv_unsigned_in_range _ hb) as R. change (bv_modulus 8) with (2 ^ 8) in R.
      destruct (Z.eq_dec (bv_unsigned hb) 255) as [E255|E255].
      - rewrite E255 in E2. vm_compute in E2. discriminate E2.
      - rewrite Z.mod_small in E2 by (clear E2; lia). lia. }
    set (m2 := fun x : word => if (bv_unsigned x =? 0)%Z then Some b' else m x).
    assert (M2a : m2 (wa 0) = Some b') by (subst m2; cbn beta; rewrite wa_unsigned, Z.eqb_refl by lia; reflexivity).
    assert (M2o : forall x : word, bv_unsigned x <> 0 -> m2 x = m x).
    { intros x Hx. subst m2; cbn beta. destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E]; [lia | reflexivity]. }
    assert (M2z : forall z, 0 <= z < 2 ^ 64 -> z <> 0 -> m2 (wa z) = m (wa z)).
    { intros z Hz Hza. apply M2o. rewrite wa_unsigned by lia. exact Hza. }
    assert (WV2 : forall x : word, wview asegs m x <> None -> wview asegs m2 x <> None).
    { intros x Wx. unfold wview in *. destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E].
      - replace x with (wa 0) by (apply bv_eq; rewrite wa_unsigned by lia; symmetry; exact E). rewrite M2a. discriminate.
      - rewrite (M2o x E). exact Wx. }
    assert (RD2 : forall x : word, bv_unsigned x <> 0 -> mrd asegs m2 x = mrd asegs m x).
    { intros x Hx. unfold mrd. rewrite (M2o x Hx). reflexivity. }
    assert (NC : ~ aconst_addr 0).
    { intros C. cbv in C.
      repeat (destruct C as [C|C]; [destruct C as [C _]; exact (C eq_refl)|]).
      destruct C as [C _]; exact (C eq_refl). }
    assert (AC2 : ACONST m2).
    { eapply ACONST_ext; [exact AC0 | | |].
      - intros z Hz Hc. apply M2z; [exact Hz|]. intros ->. exact (NC Hc).
      - intros z Hz Wz. apply WV2. exact Wz.
      - intros z Hz.
        assert (Hz' : 0 <= z < 2 ^ 64 /\ z <> 0).
        { clear - Hz. unfold sh, AIMG_LO, AIMG_TOP in Hz. rewrite ASHADOW_BASE_val in Hz. Z.div_mod_to_equations. lia. }
        destruct Hz' as [Hz' Hza].
        rewrite RD2 by (rewrite wa_unsigned by lia; exact Hza).
        pose proof AC0 as (_ & _ & (_ & _ & SS)). exact (proj2 (SS z Hz)). }
    assert (MI2 : mem_inv asegs m2).
    { intros x bx Hx. destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E].
      - assert (Ex : x = wa 0) by (apply bv_eq; rewrite wa_unsigned by lia; exact E). rewrite Ex. vm_compute. reflexivity.
      - rewrite (M2o x E) in Hx. exact (MI0 _ _ Hx). }
    assert (XP2 : xpres H LB spz [(p, p + 24)] m m2).
    { intros z Hz [Cz Xz]. assert (Hza : z <> 0) by (intros ->; exact (ms_client0 Cz)).
      split; [exact (M2z z Hz Hza) | intros Wv; apply WV2; exact Wv]. }
    destruct (WK m2 AC2 MI2 XP2) as [FW2 _].
    pose proof (FW2 0 ltac:(unfold nw in NP; lia)) as F2.
    rewrite WZ in F2. change (0 + 4 * 0) with 0 in F2.
    destruct (ms_fld_hd m2 0 (Znth 0 ws) b' M2a F2) as [r E].
    apply NE. rewrite Ehb, E. reflexivity.
  Qed.

  Definition ms_spent (sb : sbuf) : Z := ms_phi sb.

  Definition ms_lbk (cs : list Z) (sb : sbuf) (LBk : list block) (pidk : bptr) : Prop :=
    match sb with
    | SShort => LBk = LB
    | SLong d asz => LBk = (pidk, d, asz) :: LB /\ ~ In pidk (map blk_id LB) /\ ablock_range H d asz
                     /\ (asz = 48 \/ asz <= 2 * Zlen cs)
    end.

  Definition ms_mem (cs : list Z) (sb : sbuf) (LBk : list block) (pidk : bptr) (sk : as_St H) (mk : mem) : Prop :=
    mem_inv asegs mk /\ stk asegs mk lo spz /\ (exists e, rw_cells asegs mk (errno_addr tp) [C4 e]) /\ as_rauxv_ok H mk B
    /\ ACONST mk /\ as_RFS H LF mk /\ stack0 mk lo shi
    /\ as_RHEAP H sk LBk mk /\ lb_own LBk mk
    /\ rw_cells asegs mk (spz - 80) FRAME
    /\ xpres H LB spz [(p, p + 24)] m mk
    /\ strA LBk mk p sb cs /\ spb_blk LBk mk sb pidk /\ ms_lbk cs sb LBk pidk
    /\ addressable mk p 24 /\ wr_at asegs mk p 24
    /\ as_AL H sk >= as_AL H s - ms_spent sb
    /\ Zlen cs <= 4 * nw.

  Definition MSCS : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

  Lemma ms_fsr : forall mk, as_RFS H LF mk -> as_FSB H <= p /\ p + 24 <= as_FSB H + AFS_SIZE.
  Proof.
    intros mk RF. destruct PFF as (f & Hf & F1 & F2).
    destruct (ah_RFS_range H HH LF mk RF) as [_ RR]. destruct (RR f Hf) as (K0 & K1 & K2 & _).
    unfold AFS_HDR in K1. lia.
  Qed.

  Lemma ms_objwin : forall LBx mk, as_RFS H LF mk -> obj_win H LBx LF (spz - 80) lo p 24.
  Proof.
    intros LBx mk RF. destruct (ms_fsr mk RF) as [F1 F2].
    destruct OBJ as (_ & _ & _ & _ & OC & SD).
    split; [right; right; right; right; left; lia|].
    split.
    { right; right; right; right; right; left. split; [apply sh_mono; lia|].
      pose proof (sh_mono (p + 24) (as_FSB H + AFS_SIZE) F2) as K. rewrite v4_nsh24.
      assert (E : sh (p + 24) = sh p + 3) by (unfold sh; Z.div_mod_to_equations; lia). lia. }
    split; [right; right; right; right; left; cbn [fst snd]; lia|].
    split; [right; destruct PFF as (f & Hf & K1 & K2); exists f; cbn [fst snd]; split; [exact Hf | lia]|].
    split; [exact OC|]. pose proof LOR as [LO1 LO2]. unfold MKSTR_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2. lia.
  Qed.

  Lemma ms_spent_step : forall cs sb, Zlen cs = str_cap sb -> (forall d asz, sb = SLong d asz -> 48 <= asz) ->
    ms_spent sb + spb_cost H sb cs <= ms_spent (SLong 0 (str_grow sb)).
  Proof.
    intros cs sb FULL A48. pose proof (rt_bp_cost H HHb) as [CF CM].
    unfold spb_cost. rewrite (proj2 (Z.eqb_eq _ _) FULL). rewrite CM, CF.
    unfold ms_spent, ms_phi, ICM. destruct sb as [|d asz]; cbn [str_grow spb_old].
    - destruct (Z.leb_spec 48 64512); destruct (Z.ltb_spec 64512 48); lia.
    - pose proof (A48 d asz eq_refl).
      destruct (Z.leb_spec (2 * asz) 64512); destruct (Z.ltb_spec 64512 asz); destruct (Z.ltb_spec 64512 (2 * asz)); lia.
  Qed.

  Lemma ms_spent_le_cost : forall cs sb LBk pidk, ms_lbk cs sb LBk pidk -> Zlen cs <= 4 * nw -> 0 <= Zlen cs ->
    ms_spent sb + spb_cost H sb cs <= ms_cost H nw.
  Proof.
    intros cs sb LBk pidk LK ZB Z0. pose proof (rt_bp_cost H HHb) as [CF CM].
    unfold ms_cost. fold nw. assert (NW0 : 0 <= nw) by (unfold nw, Zlen; lia).
    unfold spb_cost. rewrite !CM, !CF. unfold ms_spent, ms_phi, ICM.
    destruct (Z.eqb_spec (Zlen cs) (str_cap sb)) as [FULL|NF].
    - destruct sb as [|d asz]; cbn [str_grow spb_old str_cap] in *; unfold SSO_CAP in FULL.
      + destruct (Z.leb_spec 48 64512); destruct (Z.leb_spec (16 * nw + 96) 64512); lia.
      + destruct LK as (_ & _ & ABR & ASZ). pose proof ABR as (_ & _ & An & _).
        destruct (Z.ltb_spec 64512 asz); destruct (Z.leb_spec (2 * asz) 64512); destruct (Z.leb_spec (16 * nw + 96) 64512); lia.
    - destruct sb as [|d asz].
      + destruct (Z.leb_spec (16 * nw + 96) 64512); lia.
      + destruct LK as (_ & _ & ABR & ASZ). pose proof ABR as (_ & _ & An & _).
        destruct (Z.ltb_spec 64512 asz); destruct (Z.leb_spec (16 * nw + 96) 64512); lia.
  Qed.

  Lemma ms_x_apart : forall cs sb LBk pidk sk mk, strA LBk mk p sb cs -> spb_blk LBk mk sb pidk -> as_RHEAP H sk LBk mk ->
    Forall (fun iv : Z * Z => spz <= fst iv \/ snd iv <= spz - 80) ((p, p + 24) :: spb_x sb).
  Proof.
    intros cs sb LBk pidk sk mk RP BK RH.
    pose proof LOR as [LO1 LO2]. unfold MKSTR_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof SPR as (SPL & SPH & SP16). unfold MKSTR_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in SPL.
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    destruct OBJ as (_ & _ & _ & _ & _ & SD).
    apply Forall_cons; [cbn [fst snd]; lia|].
    destruct sb as [|d asz]; cbn [spb_x]; [apply Forall_nil|].
    destruct BK as [HIn _].
    pose proof (ah_blocks H HH _ _ _ _ RH HIn) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    cbn [blk_addr blk_size fst snd] in B0, B16, Bn, BI, BC, BF, BAPP.
    pose proof (sh_nsh_high d asz ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as D2. unfold AHI_LO in D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
  Qed.

  Lemma ms_call_pb : forall (msF1 : machine_state) (mo1 : Model) (sk1 : as_St H) (m1 : mem) (R1 : bvmap 5 word)
                            (cs : list Z) (sb : sbuf) (LBk : list block) (pidk : bptr) (c ra' : Z) (Q' : config -> Prop),
    as_VIS H sk1 msF1 = MS R1 F (Z_to_bv 64 SPB_ENTRY) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 1 = Z_to_bv 64 ra' -> getr R1 2 = Z_to_bv 64 (spz - 80) -> getr R1 4 = tp ->
    getr R1 10 = Z_to_bv 64 p -> getr R1 11 = Z_to_bv 64 c ->
    1 <= c <= 255 -> Zlen cs < 4 * nw -> 0 <= ra' < 2 ^ 64 -> ra' mod 2 = 0 ->
    as_AKREL H sk1 (mkCfg msF1 mo1) ->
    ms_mem cs sb LBk pidk sk1 m1 ->
    (forall (msF2 : machine_state) (mo2 : Model) (sk2 : as_St H) (m2 : mem) (R2 : bvmap 5 word) (sb2 : sbuf) (LB2 : list block)
            (pid2 : bptr),
        as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 ra') fc None m2 (seg_rom asegs) -> rfull R2 ->
        (forall r, In r MSCS -> getr R2 r = getr R1 r) ->
        as_AKREL H sk2 (mkCfg msF2 mo2) -> as_MPRES H mo1 mo2 ->
        ms_mem (cs ++ [c]) sb2 LB2 pid2 sk2 m2 ->
        as_SR H Q' (mkCfg msF2 mo2)) ->
    as_SR H Q' (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 sk1 m1 R1 cs sb LBk pidk c ra' Q' VIS1 HF1 G1 G2 G4 G10 G11 CR ZL RAR RAE KR1 MM K.
    destruct MM as (MI1 & ST1 & (e1 & ERR1) & RA1 & AC1 & RF1 & S01 & RH1 & OW1 & FR1 & XP1 & REP1 & BLK1 & LK1 & ADV1 & WP1 & AL1 & ZB1).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold MKSTR_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2, SPL.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (ZL0 : 0 <= Zlen cs) by (unfold Zlen; lia).
    assert (NW0 : 0 <= nw) by (unfold nw, Zlen; lia).

    assert (GRW : str_grow sb <= 2 ^ 28).
    { destruct sb as [|d asz]; cbn [str_grow]; [lia|]. destruct LK1 as (_ & _ & _ & ASZ). unfold nw in *. destruct ASZ; lia. }
    assert (AOK : Zlen cs = str_cap sb -> as_alloc_ok H sk1 LBk (str_grow sb) /\ spb_cost H sb cs <= as_AL H sk1).
    { intros FULL. split.
      - apply (rt_bp_live H HHb sk1 LBk m1 (str_grow sb) RH1); [destruct sb; cbn [str_grow]; [lia|]; destruct LK1 as (_ & _ & (_ & _ & An & _) & _); lia | | |].
        + destruct sb as [|d asz]; cbn [str_grow] in *.
          * rewrite LK1. pose proof (nsmall_bounds 48 ltac:(lia)). unfold nw in *. lia.
          * destruct LK1 as (E & _ & (_ & _ & An & _) & _). rewrite E, lb_small_cons. cbn [blk_size fst snd].
            cbn [str_cap] in FULL. unfold nsmall. destruct (Z.leb_spec asz 64512); destruct (Z.leb_spec (2 * asz) 64512); unfold nw in *; lia.
        + destruct sb as [|d asz]; [rewrite LK1; lia|]. destruct LK1 as (E & _). rewrite E. cbn [length]. lia.
        + destruct sb as [|d asz]; cbn [str_grow] in *.
          * rewrite LK1. pose proof (nlg_bounds 48). lia.
          * destruct LK1 as (E & _). rewrite E, nlarge_cons. pose proof (nlg_bounds (blk_size (pidk, d, asz))). pose proof (nlg_bounds (2 * asz)). lia.
      - pose proof (ms_spent_le_cost cs sb LBk pidk LK1 ltac:(lia) ZL0). pose proof (ah_costs H HH) as (C0 & _ & F0 & _).
        assert (0 <= ms_spent sb) by (destruct sb; unfold ms_spent, ms_phi; [lia|]; destruct LK1 as (_ & _ & (_ & _ & An & _) & _);
                                      destruct (Z.ltb_spec 64512 asz); lia).
        fold nw in CST. lia. }
    rewrite (rfull_eq R1 HF1) in VIS1.
    pose proof (ms_objwin LBk m1 RF1) as OWn.
    eapply (ah_seq H HH).
    { eapply (spb_ok H HH) with (c := c) (p := p) (sb := sb) (cs := cs) (pid := pidk) (LB := LBk) (LBo := LBk) (LF := LF) (lo := lo) (B := B)
          (shi := shi) (errv := e1);
        [ exact VIS1 | exact G10 | exact G11 | lia | exact REP1 | exact BLK1 | exact P8 | exact ADV1 | exact PFF
        | rewrite G2, u64_of_Z by lia; exact OWn | exact PBAND | exact WP1 | exact OW1
        | split; [intros bb Hb; exact Hb | split; [exact (ah_nodup H HH _ _ _ RH1) | destruct sb; [exact I | exact (proj1 BLK1)]]]
        | exact GRW | exact AOK | exact TRO
        | exact RH1 | exact KR1 | exact RA1 | rewrite G2, u64_of_Z by lia; lia | rewrite G2, u64_of_Z by lia; Z.div_mod_to_equations; lia
        | rewrite G2, u64_of_Z by lia; lia | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo (spz - 80) spz ST1 ltac:(lia)))
        | exact LO1 | rewrite G2, u64_of_Z by lia; unfold SPB_STACK, AOPNEW_STACK, AMALLOC_STACK; lia
        | rewrite G4; exact ERR1 | exact MI1 | rewrite G4; exact TPV | exact AC1 | exact RF1 | exact S01
        | rewrite G2, u64_of_Z by lia; lia ]. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & sk2 & LB2 & LBo2
                      & sb2 & pid2 & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & XP2 & RH2 & REP2 & BLK2 & CASE & ADV2 & WP2 & OW2
                      & RF2 & AC2 & S02 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite G1 in VIS2. rewrite (ret_pc_even ra' RAR RAE) in VIS2.
    rewrite G2, u64_of_Z in ST2, XP2 by lia. rewrite G4 in ERR2.
    pose proof (ms_x_apart cs sb LBk pidk sk1 m1 REP1 BLK1 RH1) as XAP.
    eapply (K msF2 mo2 sk2 m2 _ sb2 LB2 pid2 VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - intros r Hr. cbn [In MSCS] in Hr.
      repeat (destruct Hr as [<-|Hr]; [first [reflexivity | cbn [getr]; rewrite G1; reflexivity | symmetry; exact G1] |]). destruct Hr.
    - exact KR2.
    - exact MP2.
    - split; [exact MI2|].
      split.
      { eapply (stk_merge asegs); [exact ST2 | | lia].
        eapply (xpres_stk H); [exact XP2 | exact (proj2 (stk_split asegs m1 lo (spz - 80) spz ST1 ltac:(lia))) | lia |].
        eapply Forall_impl; [|exact XAP]. intros [l h] Hlh. cbn [fst snd] in *. lia. }
      split; [exists errv2; exact ERR2|].
      split; [exact RA2|]. split; [exact AC2|]. split; [exact RF2|]. split; [exact S02|].
      split; [exact RH2|].
      split; [destruct CASE as [(_ & _ & -> & _ & ->)|(_ & _ & d' & _ & -> & _ & ->)]; exact OW2|].
      split.
      { eapply (xpres_rw_cells H); [exact XP2 | exact FR1 |]. unfold FRAME. rewrite v4_cells_size_map_C8'. cbn [length Z.of_nat].
        split; [left; lia|]. eapply Forall_impl; [|exact XAP]. intros [l h] Hlh. cbn [fst snd] in *. lia. }
      split.
      { eapply (xpres_trans H); [exact XP1|].
        assert (XPw : xpres H LB spz ((p, p + 24) :: spb_x sb) m1 m2).
        { eapply (xpres_weaken H); [exact XP2 | lia | | intros a Ha; exact Ha].
          intros bb Hb. destruct sb as [|d asz]; [rewrite LK1; exact Hb|]. destruct LK1 as (E & _). rewrite E. right. exact Hb. }
        destruct sb as [|d asz]; [exact XPw|].
        destruct LK1 as (E & NI & _ & _). rewrite E in RH1.
        eapply (xpres_drop_fresh H HH LB spz [(p, p + 24)] m1 m2 sk1 m1 pidk d asz RH1 NI ltac:(lia)). exact XPw. }
      split; [exact REP2|]. split; [exact BLK2|].
      split.
      { destruct CASE as [(NF & -> & -> & -> & _)|(FULL & NI2 & d' & -> & -> & ABR2 & _)].
        - destruct sb as [|d asz]; cbn [ms_lbk] in *; [exact LK1|].
          destruct LK1 as (E & NI & ABR & ASZ). split; [exact E|]. split; [exact NI|]. split; [exact ABR|].
          rewrite Zlen_app1. destruct ASZ; [left | right]; lia.
        - destruct sb as [|d asz]; cbn [ms_lbk spb_LB str_grow] in *.
          + rewrite LK1. rewrite LK1 in NI2. unfold spb_LB. split; [reflexivity|]. split; [exact NI2|]. split; [exact ABR2 | left; reflexivity].
          + destruct LK1 as (E & NI & ABR & ASZ). rewrite E. rewrite E in NI2.
            pose proof (ah_lb_remove H HH) as (L1 & L2 & L3). unfold spb_LB. rewrite (L1 pidk d asz LB NI).
            split; [reflexivity|]. split; [intros K'; apply NI2; right; exact K'|]. split; [exact ABR2|].
            right. rewrite Zlen_app1. cbn [str_cap] in FULL. lia. }
      split; [exact ADV2|]. split; [exact WP2|].
      split.
      { destruct CASE as [(NF & -> & -> & -> & _)|(FULL & NI2 & d' & -> & -> & ABR2 & _)].
        - unfold spb_cost in AL2. destruct (Z.eqb_spec (Zlen cs) (str_cap sb)); [lia|]. lia.
        - assert (A48 : forall d asz, sb = SLong d asz -> 48 <= asz).
          { intros d asz E. rewrite E in LK1. destruct LK1 as (_ & _ & _ & ASZ). rewrite E in FULL. cbn [str_cap] in FULL.
            destruct ASZ; [lia|]. pose proof REP1 as RP. rewrite E in RP.
            destruct (strA_long_facts _ _ _ _ _ _ RP) as (_ & _ & _ & AM & AMIN & _). Z.div_mod_to_equations. lia. }
          pose proof (ms_spent_step cs sb FULL A48) as STEP. unfold ms_spent, ms_phi in STEP, AL1 |- *.
            revert STEP AL1 AL2. clear. destruct sb as [|d0 asz0]; cbn [str_grow];
            [ destruct (Z.ltb_spec 64512 48); cbv iota beta; intros; lia
            | destruct (Z.ltb_spec 64512 asz0); destruct (Z.ltb_spec 64512 (2 * asz0)); cbv iota beta; intros; lia ]. }
      rewrite Zlen_app1. lia.
  Qed.

  Lemma ms_exit : forall (msFx : machine_state) (mox : Model) (sx : as_St H) (mx : mem) (Rx : bvmap 5 word)
                         (cs : list Z) (sb : sbuf) (LBk : list block) (pidk : bptr),
    cs = ms_chars ws ->
    as_VIS H sx msFx = MS Rx F (Z_to_bv 64 MS_EXIT) fc None mx (seg_rom asegs) -> rfull Rx ->
    getr Rx 2 = Z_to_bv 64 (spz - 80) -> getr Rx 3 = gp -> getr Rx 4 = tp ->
    getr Rx 25 = s9 -> getr Rx 26 = s10 -> getr Rx 27 = s11 ->
    as_AKREL H sx (mkCfg msFx mox) -> as_MPRES H mo mox ->
    ms_mem cs sb LBk pidk sx mx ->
    as_SR H Q (mkCfg msFx mox).
  Proof.
    intros msFx mox sx mx Rx cs sb LBk pidk ECS VISx HFx G2 G3 G4 G25 G26 G27 KRx MPx MM.
    destruct MM as (MI1 & ST1 & (e1 & ERR1) & RA1 & AC1 & RF1 & S01 & RH1 & OW1 & FR1 & XP1 & REP1 & BLK1 & LK1 & ADV1 & WP1 & AL1 & ZB1).
    pose proof SPR as (SPL & SPH & SP16). unfold MKSTR_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in SPL.
    destruct (ms_BX_ok Rx F fc mx spz s8 s7 s6 s5 s4 s3 s2 s1 s0 ra G2 FR1 ltac:(lia) SPH)
      as (R' & Hms & K1 & K2 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & KK).
    assert (HF' : rfull R') by exact (msteps_full asegs _ _ Hms HFx).
    assert (K3 : getr R' 3 = gp) by (rewrite (KK 3%bv ltac:(inb)); exact G3).
    assert (K4 : getr R' 4 = tp) by (rewrite (KK 4%bv ltac:(inb)); exact G4).
    assert (K25 : getr R' 25 = s9) by (rewrite (KK 25%bv ltac:(inb)); exact G25).
    assert (K26 : getr R' 26 = s10) by (rewrite (KK 26%bv ltac:(inb)); exact G26).
    assert (K27 : getr R' 27 = s11) by (rewrite (KK 27%bv ltac:(inb)); exact G27).
    eapply (sr_evt H HH) with
      (P := fun ms => ms = MS (mkR ra sp gp tp (getr R' 5) (getr R' 6) (getr R' 7) s0 s1 (getr R' 10)
                                   (getr R' 11) (getr R' 12) (getr R' 13) (getr R' 14) (getr R' 15) (getr R' 16) (getr R' 17)
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31))
                              F (ret_pc ra) fc None mx (seg_rom asegs));
      [exact KRx | exact VISx | |].
    { eapply evt_of_msteps; [exact Hms|]. rewrite (rfull_eq R' HF'). apply ms_ret_ok.
      rewrite K1, K2, K3, K4, K8, K9, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. unfold wz. rewrite <- spz_sp'. reflexivity. }
    intros msF2 mo2 KR2 MP2 HP. cbv beta in HP.
    exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 10), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14),
      (getr R' 15), (getr R' 16), (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), mx, e1, sx, LBk, sb, pidk.
    cbn [cfg_ms cfg_model]. rewrite SPZ. rewrite ECS in REP1.
    split; [exact HP|]. split; [exact KR2|]. split; [eapply (ah_mpres_trans H HH); eassumption|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact RA1|]. split; [exact XP1|].
    split; [exact RH1|]. split; [exact REP1|]. split; [exact BLK1|].
    split; [destruct sb as [|d asz]; cbn [ms_lbk] in LK1; [exact LK1 | destruct LK1 as (E & NI & ABR & BZ); split; [exact E | split; [exact NI | split; [exact ABR | split; [rewrite <- ECS; exact BZ | rewrite <- ECS; exact ZB1]]]]]|].
    split; [exact ADV1|]. split; [exact WP1|]. split; [exact OW1|].
    split; [exact RF1|]. split; [exact AC1|]. split; [exact S01|].
    unfold ms_spent in AL1. exact AL1.
  Qed.

  Definition mk_regs (R : bvmap 5 word) (a r : Z) : Prop :=
    getr R 2 = Z_to_bv 64 (spz - 80) /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = Z_to_bv 64 a /\ getr R 18 = Z_to_bv 64 a
    /\ getr R 9 = Z_to_bv 64 p /\ getr R 20 = Z_to_bv 64 0x7fff8000 /\ getr R 19 = Z_to_bv 64 (4 * r)
    /\ getr R 21 = Z_to_bv 64 0xff0000 /\ getr R 22 = Z_to_bv 64 0xff00 /\ getr R 23 = Z_to_bv 64 (2 ^ 64 - 4)
    /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11.

  Definition MKR : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv.
  Lemma mk_regs_keep : forall R R' a r, mk_regs R a r -> (forall q, In q MKR -> getr R' q = getr R q) -> mk_regs R' a r.
  Proof.
    intros R R' a r (G2 & G3 & G4 & G8 & G18 & G9 & G20 & G19 & G21 & G22 & G23 & G25 & G26 & G27) KK.
    repeat split; rewrite KK by inb; assumption.
  Qed.

  Definition ms_wctx (k r : nat) (x : Z) : Prop :=
    (k + r)%nat = length ws /\ (1 <= r)%nat /\ x = nth k ws 0 /\ 0 <= x < 2 ^ 32 /\ ms_nz ws k.

  Lemma ms_wctx_chars : forall k r x, ms_wctx k r x ->
    ms_chars ws = ms_pref ws k ++ ms_chars (x :: skipn (S k) ws).
  Proof.
    intros k r x (KR & R1 & EX & XR & NZ). rewrite (ms_chars_pref ws k); [| lia | | exact NZ].
    - rewrite (skipn_nth_cons' ws k ltac:(lia)). rewrite <- EX. reflexivity.
    - intros i Hi. pose proof (WSR (Z.of_nat i) ltac:(unfold Zlen; lia)) as K. unfold Znth in K. rewrite Nat2Z.id in K. exact K.
  Qed.

  Lemma ms_pref_len_eq : forall k, (k <= length ws)%nat -> Zlen (ms_pref ws k) = 4 * Z.of_nat k.
  Proof.
    intros k. unfold ms_pref, Zlen. generalize ws. induction k as [|k IH]; intros l Hk.
    - simpl. lia.
    - destruct l as [|x l']; [cbn in Hk; lia|].
      change (firstn (S k) (x :: l')) with (x :: firstn k l'). change (flat_map wchars (x :: firstn k l')) with (wchars x ++ flat_map wchars (firstn k l')).
      rewrite length_app. change (length (wchars x)) with 4%nat. specialize (IH l' ltac:(cbn in Hk; lia)). lia.
  Qed.

  Definition ms_kloop (k r : nat) : Prop :=
    (1 <= r)%nat -> forall (msFk : machine_state) (mok : Model) (sk : as_St H) (mk : mem) (Rk : bvmap 5 word) (sb : sbuf) (LBk : list block)
           (pidk : bptr),
      as_VIS H sk msFk = MS Rk F (Z_to_bv 64 MS_HEAD) fc None mk (seg_rom asegs) -> rfull Rk ->
      mk_regs Rk (w + 4 * Z.of_nat (S k)) (Z.of_nat r) -> as_AKREL H sk (mkCfg msFk mok) -> as_MPRES H mo mok ->
      ms_nz ws (S k) -> ms_mem (ms_pref ws (S k)) sb LBk pidk sk mk ->
      as_SR H Q (mkCfg msFk mok).

  Lemma mk_regs_exit : forall R a r, mk_regs R a r ->
    getr R 2 = Z_to_bv 64 (spz - 80) /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 25 = s9
    /\ getr R 26 = s10 /\ getr R 27 = s11.
  Proof. intros R a r (G2 & G3 & G4 & _ & _ & _ & _ & _ & _ & _ & _ & G25 & G26 & G27). repeat split; assumption. Qed.

  Lemma ms_exit_regs : forall R R' a r (L : list reg), mk_regs R a r -> (forall q, In q L -> getr R' q = getr R q) ->
    incl [2; 3; 4; 25; 26; 27]%bv L ->
    getr R' 2 = Z_to_bv 64 (spz - 80) /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 25 = s9
    /\ getr R' 26 = s10 /\ getr R' 27 = s11.
  Proof.
    intros R R' a r L RG KK INC. destruct (mk_regs_exit R a r RG) as (G2 & G3 & G4 & G25 & G26 & G27).
    repeat split; rewrite KK by (apply INC; cbn; tauto); assumption.
  Qed.

  Ltac ms_exit_tac VIS HF RG KK KR MP MM CSEQ :=
    let E := fresh in
    destruct (ms_exit_regs _ _ _ _ _ RG KK ltac:(intros q Hq; repeat (destruct Hq as [<-|Hq]; [inb|]); destruct Hq)) as (E2 & E3 & E4 & E25 & E26 & E27);
    eapply (ms_exit _ _ _ _ _ _ _ _ _ CSEQ VIS HF E2 E3 E4 E25 E26 E27 KR MP MM).

  Lemma ms_st7 : forall (k r : nat) (x : Z) (msF7 : machine_state) (mo7 : Model) (sk7 : as_St H) (m7 : mem) (R7 : bvmap 5 word)
                        (sb : sbuf) (LBk : list block) (pidk : bptr),
    ms_wctx k (S r) x -> (forall c, In c (wchars x) -> c <> 0) -> ms_kloop k r ->
    as_VIS H sk7 msF7 = MS R7 F (Z_to_bv 64 0xea75c) fc None m7 (seg_rom asegs) -> rfull R7 ->
    mk_regs R7 (w + 4 * Z.of_nat k) (Z.of_nat (S r)) -> as_AKREL H sk7 (mkCfg msF7 mo7) -> as_MPRES H mo mo7 ->
    ms_mem (ms_pref ws (S k)) sb LBk pidk sk7 m7 ->
    as_SR H Q (mkCfg msF7 mo7).
  Proof.
    intros k r x msF7 mo7 sk7 m7 R7 sb LBk pidk WC NZx KL VIS7 HF7 RG KR7 MP7 MM.
    pose proof WC as (KR & R1 & EX & XR & NZ).
    pose proof RG as (G2 & G3 & G4 & G8 & G18 & G9 & G20 & G19 & G21 & G22 & G23 & G25 & G26 & G27).
    assert (NWk : Z.of_nat k + Z.of_nat (S r) = nw) by (unfold nw, Zlen; lia).
    assert (NZ' : ms_nz ws (S k)).
    { intros i Hi c Hc. destruct (Nat.eq_dec i k) as [->|Hne]; [rewrite <- EX in Hc; exact (NZx c Hc) | exact (NZ i ltac:(lia) c Hc)]. }
    destruct (ms_B7_ok R7 F fc m7 (w + 4 * Z.of_nat k) (Z.of_nat (S r)) G8 G18 G19 G23 ltac:(unfold nw in *; lia) ltac:(lia)
                 ltac:(unfold nw in *; lia)) as (R8 & HL & HX).
    destruct r as [|r].
    -
      destruct (HX eq_refl) as [Hms KK].
      pose proof (msteps_full asegs _ _ Hms HF7) as HF8. cbn [ms_regs] in HF8.
      eapply (sr_blk H HH); [exact KR7 | exact VIS7 | exact HF7 | exact Hms |].
      intros msF8 mo8 KR8 MP8 VIS8. rewrite <- (rfull_eq R8 HF8) in VIS8.
      assert (CSEQ : ms_pref ws (S k) = ms_chars ws).
      { rewrite (ms_wctx_chars k 1 x WC). rewrite (ms_chars_cons_val x _ XR).
        rewrite skipn_all2 by lia. rewrite (wchars_val x XR) in NZx.
        assert (B0 : x mod 256 <> 0) by (apply NZx; cbn; tauto).
        assert (B1 : (x / 256) mod 256 <> 0) by (apply NZx; cbn; tauto).
        assert (B2 : (x / 256 / 256) mod 256 <> 0) by (apply NZx; cbn; tauto).
        assert (B3 : (x / 256 / 256 / 256) mod 256 <> 0) by (apply NZx; cbn; tauto).
        rewrite (proj2 (Z.eqb_neq _ _) B0), (proj2 (Z.eqb_neq _ _) B1), (proj2 (Z.eqb_neq _ _) B2), (proj2 (Z.eqb_neq _ _) B3).
        cbn [ms_chars]. rewrite app_nil_r. rewrite (ms_pref_S ws k ltac:(lia)). rewrite <- EX. reflexivity. }
      assert (MP78 : as_MPRES H mo mo8) by (eapply (ah_mpres_trans H HH); [exact MP7 | exact MP8]).
      ms_exit_tac VIS8 HF8 RG KK KR8 MP78 MM CSEQ.
    -
      destruct (HL ltac:(lia)) as (Hms & K8 & K18 & K19 & KK).
      pose proof (msteps_full asegs _ _ Hms HF7) as HF8. cbn [ms_regs] in HF8.
      eapply (sr_blk H HH); [exact KR7 | exact VIS7 | exact HF7 | exact Hms |].
      intros msF8 mo8 KR8 MP8 VIS8. rewrite <- (rfull_eq R8 HF8) in VIS8.
      eapply (KL ltac:(lia) msF8 mo8 sk7 m7 R8 sb LBk pidk VIS8 HF8).
      + split; [rewrite (KK 2%bv ltac:(inb)); exact G2|]. split; [rewrite (KK 3%bv ltac:(inb)); exact G3|].
        split; [rewrite (KK 4%bv ltac:(inb)); exact G4|].
        split; [rewrite K8; unfold wz; f_equal; lia|]. split; [rewrite K18; unfold wz; f_equal; lia|].
        split; [rewrite (KK 9%bv ltac:(inb)); exact G9|]. split; [rewrite (KK 20%bv ltac:(inb)); exact G20|].
        split; [rewrite K19; unfold wz; f_equal; lia|].
        split; [rewrite (KK 21%bv ltac:(inb)); exact G21|]. split; [rewrite (KK 22%bv ltac:(inb)); exact G22|].
        split; [rewrite (KK 23%bv ltac:(inb)); exact G23|]. split; [rewrite (KK 25%bv ltac:(inb)); exact G25|].
        split; [rewrite (KK 26%bv ltac:(inb)); exact G26 | rewrite (KK 27%bv ltac:(inb)); exact G27].
      + exact KR8.
      + eapply (ah_mpres_trans H HH); [exact MP7 | exact MP8].
      + exact NZ'.
      + exact MM.
  Qed.

  Lemma ms_st6 : forall (k r : nat) (x : Z) (msF1 : machine_state) (mo1 : Model) (sk1 : as_St H) (m1 : mem) (R1 : bvmap 5 word)
                        (sb : sbuf) (LBk : list block) (pidk : bptr),
    ms_wctx k (S r) x -> wbyte x 0 <> 0 -> wbyte x 1 <> 0 -> wbyte x 2 <> 0 -> ms_kloop k r ->
    as_VIS H sk1 msF1 = MS R1 F (Z_to_bv 64 0xea74c) fc None m1 (seg_rom asegs) -> rfull R1 ->
    mk_regs R1 (w + 4 * Z.of_nat k) (Z.of_nat (S r)) -> getr R1 24 = Z_to_bv 64 x ->
    as_AKREL H sk1 (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    ms_mem (((ms_pref ws k ++ [wbyte x 0]) ++ [wbyte x 1]) ++ [wbyte x 2]) sb LBk pidk sk1 m1 ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros k r x msF1 mo1 sk1 m1 R1 sb LBk pidk WC P0 P1 P2 KL VIS1 HF1 RG GX KR1 MP1 MM.
    pose proof WC as (KR & R1' & EX & XR & NZ).
    pose proof RG as (G2 & G3 & G4 & G8 & G18 & G9 & G20 & G19 & G21 & G22 & G23 & G25 & G26 & G27).
    pose proof (Z.mod_pos_bound x 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256) 256 ltac:(lia)).
    pose proof (Z.mod_pos_bound (x / 256 / 256) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256 / 256 / 256) 256 ltac:(lia)).
    assert (ZLk : Zlen (ms_pref ws k) = 4 * Z.of_nat k) by (apply ms_pref_len_eq; lia).
    assert (NWk : Z.of_nat k + Z.of_nat (S r) = nw) by (unfold nw, Zlen; lia).
    destruct (ms_B6_ok R1 F fc m1 p x GX G22 G21 G9 XR) as (R2 & HX & HC).
    destruct (Z.eq_dec (wbyte x 3) 0) as [BZ|BN].
    -
      destruct (HX BZ) as [Hms KK].
      pose proof (msteps_full asegs _ _ Hms HF1) as HF2. cbn [ms_regs] in HF2.
      eapply (sr_blk H HH); [exact KR1 | exact VIS1 | exact HF1 | exact Hms |].
      intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R2 HF2) in VIS2.
      assert (CSEQ : ((ms_pref ws k ++ [wbyte x 0]) ++ [wbyte x 1]) ++ [wbyte x 2] = ms_chars ws).
      { rewrite (ms_wctx_chars k (S r) x WC). rewrite (ms_chars_cons_val x _ XR).
        rewrite ?wbyte_0, ?wbyte_1, ?wbyte_2, ?wbyte_3 in *. rewrite (proj2 (Z.eqb_neq _ _) P0), (proj2 (Z.eqb_neq _ _) P1), (proj2 (Z.eqb_neq _ _) P2), (proj2 (Z.eqb_eq _ _) BZ).
        rewrite <- !app_assoc. reflexivity. }
      assert (MP12 : as_MPRES H mo mo2) by (eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]).
      ms_exit_tac VIS2 HF2 RG KK KR2 MP12 MM CSEQ.
    -
      destruct (HC BN) as (Hms & K1 & K10 & K11 & KK).
      pose proof (msteps_full asegs _ _ Hms HF1) as HF2. cbn [ms_regs] in HF2.
      eapply (sr_blk H HH); [exact KR1 | exact VIS1 | exact HF1 | exact Hms |].
      intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R2 HF2) in VIS2.
      assert (BR : 1 <= wbyte x 3 <= 255) by (rewrite ?wbyte_0, ?wbyte_1, ?wbyte_2, ?wbyte_3 in *; lia).
      eapply (ms_call_pb msF2 mo2 sk1 m1 R2 (((ms_pref ws k ++ [wbyte x 0]) ++ [wbyte x 1]) ++ [wbyte x 2]) sb LBk pidk (wbyte x 3) 0xea75c Q VIS2 HF2 K1).
      + rewrite (KK 2%bv ltac:(inb)). exact G2.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + exact K10.
      + exact K11.
      + exact BR.
      + rewrite !Zlen_app1. lia.
      + lia.
      + reflexivity.
      + exact KR2.
      + exact MM.
      + intros msF3 mo3 sk3 m3 R3 sb3 LB3 pid3 VIS3 HF3 KK3 KR3 MP3 MM3.
        assert (RG3 : mk_regs R3 (w + 4 * Z.of_nat k) (Z.of_nat (S r))).
        { eapply mk_regs_keep; [exact RG|]. intros q Hq.
          assert (Q1 : In q MSCS) by (clear - Hq; repeat (destruct Hq as [<-|Hq]; [inb|]); destruct Hq).
          assert (Q2 : In q MSK4C) by (clear - Hq; repeat (destruct Hq as [<-|Hq]; [inb|]); destruct Hq).
          rewrite (KK3 q Q1). exact (KK q Q2). }
        eapply (ms_st7 k r x msF3 mo3 sk3 m3 R3 sb3 LB3 pid3 WC ltac:(intros cc Hc; rewrite (wchars_val x XR) in Hc; rewrite ?wbyte_0, ?wbyte_1, ?wbyte_2, ?wbyte_3 in *;
                    destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; assumption) KL VIS3 HF3 RG3).
        * exact KR3.
        * eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3]].
        * replace (ms_pref ws (S k)) with ((((ms_pref ws k ++ [wbyte x 0]) ++ [wbyte x 1]) ++ [wbyte x 2]) ++ [wbyte x 3]); [exact MM3|].
          rewrite (ms_pref_S ws k ltac:(lia)), <- EX, (wchars_val x XR). rewrite ?wbyte_0, ?wbyte_1, ?wbyte_2, ?wbyte_3. rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma ms_st5 : forall (k r : nat) (x : Z) (msF1 : machine_state) (mo1 : Model) (sk1 : as_St H) (m1 : mem) (R1 : bvmap 5 word)
                        (sb : sbuf) (LBk : list block) (pidk : bptr),
    ms_wctx k (S r) x -> wbyte x 0 <> 0 -> wbyte x 1 <> 0 -> ms_kloop k r ->
    as_VIS H sk1 msF1 = MS R1 F (Z_to_bv 64 0xea734) fc None m1 (seg_rom asegs) -> rfull R1 ->
    mk_regs R1 (w + 4 * Z.of_nat k) (Z.of_nat (S r)) -> getr R1 24 = Z_to_bv 64 x ->
    as_AKREL H sk1 (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    ms_mem ((ms_pref ws k ++ [wbyte x 0]) ++ [wbyte x 1]) sb LBk pidk sk1 m1 ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros k r x msF1 mo1 sk1 m1 R1 sb LBk pidk WC P0 P1 KL VIS1 HF1 RG GX KR1 MP1 MM.
    pose proof WC as (KR & R1' & EX & XR & NZ).
    pose proof RG as (G2 & G3 & G4 & G8 & G18 & G9 & G20 & G19 & G21 & G22 & G23 & G25 & G26 & G27).
    pose proof (Z.mod_pos_bound x 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256) 256 ltac:(lia)).
    pose proof (Z.mod_pos_bound (x / 256 / 256) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256 / 256 / 256) 256 ltac:(lia)).
    assert (ZLk : Zlen (ms_pref ws k) = 4 * Z.of_nat k) by (apply ms_pref_len_eq; lia).
    assert (NWk : Z.of_nat k + Z.of_nat (S r) = nw) by (unfold nw, Zlen; lia).
    destruct (ms_B5_ok R1 F fc m1 p x GX G22 G21 G9 XR) as (R2 & HX & HC).
    destruct (Z.eq_dec (wbyte x 2) 0) as [BZ|BN].
    -
      destruct (HX BZ) as [Hms KK].
      pose proof (msteps_full asegs _ _ Hms HF1) as HF2. cbn [ms_regs] in HF2.
      eapply (sr_blk H HH); [exact KR1 | exact VIS1 | exact HF1 | exact Hms |].
      intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R2 HF2) in VIS2.
      assert (CSEQ : (ms_pref ws k ++ [wbyte x 0]) ++ [wbyte x 1] = ms_chars ws).
      { rewrite (ms_wctx_chars k (S r) x WC). rewrite (ms_chars_cons_val x _ XR).
        rewrite ?wbyte_0, ?wbyte_1, ?wbyte_2, ?wbyte_3 in *. rewrite (proj2 (Z.eqb_neq _ _) P0), (proj2 (Z.eqb_neq _ _) P1), (proj2 (Z.eqb_eq _ _) BZ).
        rewrite <- !app_assoc. reflexivity. }
      assert (MP12 : as_MPRES H mo mo2) by (eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]).
      ms_exit_tac VIS2 HF2 RG KK KR2 MP12 MM CSEQ.
    -
      destruct (HC BN) as (Hms & K1 & K10 & K11 & KK).
      pose proof (msteps_full asegs _ _ Hms HF1) as HF2. cbn [ms_regs] in HF2.
      eapply (sr_blk H HH); [exact KR1 | exact VIS1 | exact HF1 | exact Hms |].
      intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R2 HF2) in VIS2.
      assert (BR : 1 <= wbyte x 2 <= 255) by (rewrite ?wbyte_0, ?wbyte_1, ?wbyte_2, ?wbyte_3 in *; lia).
      eapply (ms_call_pb msF2 mo2 sk1 m1 R2 ((ms_pref ws k ++ [wbyte x 0]) ++ [wbyte x 1]) sb LBk pidk (wbyte x 2) 0xea74c Q VIS2 HF2 K1).
      + rewrite (KK 2%bv ltac:(inb)). exact G2.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + exact K10.
      + exact K11.
      + exact BR.
      + rewrite !Zlen_app1. lia.
      + lia.
      + reflexivity.
      + exact KR2.
      + exact MM.
      + intros msF3 mo3 sk3 m3 R3 sb3 LB3 pid3 VIS3 HF3 KK3 KR3 MP3 MM3.
        assert (RG3 : mk_regs R3 (w + 4 * Z.of_nat k) (Z.of_nat (S r))).
        { eapply mk_regs_keep; [exact RG|]. intros q Hq.
          assert (Q1 : In q MSCS) by (clear - Hq; repeat (destruct Hq as [<-|Hq]; [inb|]); destruct Hq).
          assert (Q2 : In q MSK4C) by (clear - Hq; repeat (destruct Hq as [<-|Hq]; [inb|]); destruct Hq).
          rewrite (KK3 q Q1). exact (KK q Q2). }
        eapply (ms_st6 k r x msF3 mo3 sk3 m3 R3 sb3 LB3 pid3 WC P0 P1 BN KL VIS3 HF3 RG3).
        * rewrite (KK3 24%bv ltac:(inb)), (KK 24%bv ltac:(inb)). exact GX.
        * exact KR3.
        * eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3]].
        * exact MM3.
  Qed.

  Lemma ms_st4 : forall (k r : nat) (x : Z) (msF1 : machine_state) (mo1 : Model) (sk1 : as_St H) (m1 : mem) (R1 : bvmap 5 word)
                        (sb : sbuf) (LBk : list block) (pidk : bptr),
    ms_wctx k (S r) x -> wbyte x 0 <> 0 -> ms_kloop k r ->
    as_VIS H sk1 msF1 = MS R1 F (Z_to_bv 64 0xea71c) fc None m1 (seg_rom asegs) -> rfull R1 ->
    mk_regs R1 (w + 4 * Z.of_nat k) (Z.of_nat (S r)) -> getr R1 24 = Z_to_bv 64 x ->
    as_AKREL H sk1 (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    ms_mem (ms_pref ws k ++ [wbyte x 0]) sb LBk pidk sk1 m1 ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros k r x msF1 mo1 sk1 m1 R1 sb LBk pidk WC P0 KL VIS1 HF1 RG GX KR1 MP1 MM.
    pose proof WC as (KR & R1' & EX & XR & NZ).
    pose proof RG as (G2 & G3 & G4 & G8 & G18 & G9 & G20 & G19 & G21 & G22 & G23 & G25 & G26 & G27).
    pose proof (Z.mod_pos_bound x 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256) 256 ltac:(lia)).
    pose proof (Z.mod_pos_bound (x / 256 / 256) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 256 / 256 / 256) 256 ltac:(lia)).
    assert (ZLk : Zlen (ms_pref ws k) = 4 * Z.of_nat k) by (apply ms_pref_len_eq; lia).
    assert (NWk : Z.of_nat k + Z.of_nat (S r) = nw) by (unfold nw, Zlen; lia).
    destruct (ms_B4_ok R1 F fc m1 p x GX G22 G21 G9 XR) as (R2 & HX & HC).
    destruct (Z.eq_dec (wbyte x 1) 0) as [BZ|BN].
    -
      destruct (HX BZ) as [Hms KK].
      pose proof (msteps_full asegs _ _ Hms HF1) as HF2. cbn [ms_regs] in HF2.
      eapply (sr_blk H HH); [exact KR1 | exact VIS1 | exact HF1 | exact Hms |].
      intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R2 HF2) in VIS2.
      assert (CSEQ : ms_pref ws k ++ [wbyte x 0] = ms_chars ws).
      { rewrite (ms_wctx_chars k (S r) x WC). rewrite (ms_chars_cons_val x _ XR).
        rewrite ?wbyte_0, ?wbyte_1, ?wbyte_2, ?wbyte_3 in *. rewrite (proj2 (Z.eqb_neq _ _) P0), (proj2 (Z.eqb_eq _ _) BZ). reflexivity. }
      assert (MP12 : as_MPRES H mo mo2) by (eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]).
      ms_exit_tac VIS2 HF2 RG KK KR2 MP12 MM CSEQ.
    -
      destruct (HC BN) as (Hms & K1 & K10 & K11 & KK).
      pose proof (msteps_full asegs _ _ Hms HF1) as HF2. cbn [ms_regs] in HF2.
      eapply (sr_blk H HH); [exact KR1 | exact VIS1 | exact HF1 | exact Hms |].
      intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R2 HF2) in VIS2.
      assert (BR : 1 <= wbyte x 1 <= 255) by (rewrite ?wbyte_0, ?wbyte_1, ?wbyte_2, ?wbyte_3 in *; lia).
      eapply (ms_call_pb msF2 mo2 sk1 m1 R2 (ms_pref ws k ++ [wbyte x 0]) sb LBk pidk (wbyte x 1) 0xea734 Q VIS2 HF2 K1).
      + rewrite (KK 2%bv ltac:(inb)). exact G2.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + exact K10.
      + exact K11.
      + exact BR.
      + rewrite !Zlen_app1. lia.
      + lia.
      + reflexivity.
      + exact KR2.
      + exact MM.
      + intros msF3 mo3 sk3 m3 R3 sb3 LB3 pid3 VIS3 HF3 KK3 KR3 MP3 MM3.
        assert (RG3 : mk_regs R3 (w + 4 * Z.of_nat k) (Z.of_nat (S r))).
        { eapply mk_regs_keep; [exact RG|]. intros q Hq.
          assert (Q1 : In q MSCS) by (clear - Hq; repeat (destruct Hq as [<-|Hq]; [inb|]); destruct Hq).
          assert (Q2 : In q MSK4C) by (clear - Hq; repeat (destruct Hq as [<-|Hq]; [inb|]); destruct Hq).
          rewrite (KK3 q Q1). exact (KK q Q2). }
        eapply (ms_st5 k r x msF3 mo3 sk3 m3 R3 sb3 LB3 pid3 WC P0 BN KL VIS3 HF3 RG3).
        * rewrite (KK3 24%bv ltac:(inb)), (KK 24%bv ltac:(inb)). exact GX.
        * exact KR3.
        * eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3]].
        * exact MM3.
  Qed.

  Lemma ms_word_at : forall (k : nat) cs sb LBk pidk sk mk, (k < length ws)%nat ->
    ms_mem cs sb LBk pidk sk mk ->
    fldA mk (w + 4 * Z.of_nat k) 4 (nth k ws 0) /\
    exists kk, LbB_Kit.shk mk (w + 4 * Z.of_nat k) kk /\ (kk = 0 \/ (w + 4 * Z.of_nat k) mod 8 + 4 <= kk < 8).
  Proof.
    intros k cs sb LBk pidk sk mk Hk MM.
    destruct MM as (MI1 & _ & _ & _ & AC1 & _ & _ & _ & _ & _ & XP1 & _).
    destruct (WK mk AC1 MI1 XP1) as [FW ACC].
    split.
    - pose proof (FW (Z.of_nat k) ltac:(unfold Zlen; lia)) as K. unfold Znth in K. rewrite Nat2Z.id in K. exact K.
    - apply (ms_shk_word mk w (4 * Zlen ws) (w + 4 * Z.of_nat k) ACC); [lia | unfold Zlen; lia |].
      clear - W4. Z.div_mod_to_equations. lia.
  Qed.

  Lemma ms_st3 : forall (k r : nat) (msF1 : machine_state) (mo1 : Model) (sk1 : as_St H) (m1 : mem) (R1 : bvmap 5 word)
                        (sb : sbuf) (LBk : list block) (pidk : bptr),
    (k + S r)%nat = length ws -> ms_kloop k r ->
    as_VIS H sk1 msF1 = MS R1 F (Z_to_bv 64 MS_HEAD) fc None m1 (seg_rom asegs) -> rfull R1 ->
    mk_regs R1 (w + 4 * Z.of_nat k) (Z.of_nat (S r)) -> as_AKREL H sk1 (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    ms_nz ws k -> ms_mem (ms_pref ws k) sb LBk pidk sk1 m1 ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros k r msF1 mo1 sk1 m1 R1 sb LBk pidk KR KL VIS1 HF1 RG KR1 MP1 NZ MM.
    pose proof RG as (G2 & G3 & G4 & G8 & G18 & G9 & G20 & G19 & G21 & G22 & G23 & G25 & G26 & G27).
    destruct (ms_word_at k _ sb LBk pidk sk1 m1 ltac:(lia) MM) as (FX & kk & SK & KC).
    assert (EXx : exists x, x = nth k ws 0) by (eexists; reflexivity). destruct EXx as [x EX]. rewrite <- EX in FX.
    assert (XR : 0 <= x < 2 ^ 32).
    { pose proof (WSR (Z.of_nat k) ltac:(unfold Zlen; lia)) as K. unfold Znth in K. rewrite Nat2Z.id in K. rewrite EX. exact K. }
    assert (WC : ms_wctx k (S r) x).
    { split; [exact KR|]. split; [lia|]. split; [exact EX|]. split; [exact XR | exact NZ]. }
    assert (ZLk : Zlen (ms_pref ws k) = 4 * Z.of_nat k) by (apply ms_pref_len_eq; lia).
    assert (NWk : Z.of_nat k + Z.of_nat (S r) = nw) by (unfold nw, Zlen; lia).
    assert (B3P : ms_B3pre R1 m1 (w + 4 * Z.of_nat k) p x kk).
    { split; [exact G8|]. split; [exact G18|]. split; [exact G9|]. split; [exact G20|].
      split; [exact FX|]. split; [exact SK|]. split; [exact KC|]. split; [exact XR|].
      split; [clear - W4; Z.div_mod_to_equations; lia|]. split; [lia|]. unfold nw in *. lia. }
    destruct (ms_B3_ok R1 F fc m1 (w + 4 * Z.of_nat k) p x kk B3P) as (R2 & HX & HC).
    destruct (Z.eq_dec (x mod 256) 0) as [BZ|BN].
    -
      destruct (HX BZ) as [Hms KK].
      pose proof (msteps_full asegs _ _ Hms HF1) as HF2. cbn [ms_regs] in HF2.
      eapply (sr_blk H HH); [exact KR1 | exact VIS1 | exact HF1 | exact Hms |].
      intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R2 HF2) in VIS2.
      assert (CSEQ : ms_pref ws k = ms_chars ws).
      { rewrite (ms_wctx_chars k (S r) x WC). rewrite (ms_chars_cons_val x _ XR).
        rewrite (proj2 (Z.eqb_eq _ _) BZ). rewrite app_nil_r. reflexivity. }
      assert (MP12 : as_MPRES H mo mo2) by (eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]).
      ms_exit_tac VIS2 HF2 RG KK KR2 MP12 MM CSEQ.
    -
      destruct (HC BN) as (Hms & K1 & K10 & K11 & K24 & KK).
      pose proof (msteps_full asegs _ _ Hms HF1) as HF2. cbn [ms_regs] in HF2.
      eapply (sr_blk H HH); [exact KR1 | exact VIS1 | exact HF1 | exact Hms |].
      intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R2 HF2) in VIS2.
      pose proof (Z.mod_pos_bound x 256 ltac:(lia)) as XB.
      eapply (ms_call_pb msF2 mo2 sk1 m1 R2 (ms_pref ws k) sb LBk pidk (x mod 256) 0xea71c Q VIS2 HF2 K1).
      + rewrite (KK 2%bv ltac:(inb)). exact G2.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + exact K10.
      + exact K11.
      + lia.
      + lia.
      + lia.
      + reflexivity.
      + exact KR2.
      + exact MM.
      + intros msF3 mo3 sk3 m3 R3 sb3 LB3 pid3 VIS3 HF3 KK3 KR3 MP3 MM3.
        assert (RG3 : mk_regs R3 (w + 4 * Z.of_nat k) (Z.of_nat (S r))).
        { eapply mk_regs_keep; [exact RG|]. intros q Hq.
          assert (Q1 : In q MSCS) by (clear - Hq; repeat (destruct Hq as [<-|Hq]; [inb|]); destruct Hq).
          assert (Q2 : In q MSK3C) by (clear - Hq; repeat (destruct Hq as [<-|Hq]; [inb|]); destruct Hq).
          rewrite (KK3 q Q1). exact (KK q Q2). }
        eapply (ms_st4 k r x msF3 mo3 sk3 m3 R3 sb3 LB3 pid3 WC ltac:(rewrite wbyte_0; exact BN) KL VIS3 HF3 RG3).
        * rewrite (KK3 24%bv ltac:(inb)). exact K24.
        * exact KR3.
        * eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3]].
        * rewrite wbyte_0. exact MM3.
  Qed.

  Lemma ms_loop : forall (r k : nat) (msF1 : machine_state) (mo1 : Model) (sk1 : as_St H) (m1 : mem) (R1 : bvmap 5 word)
                         (sb : sbuf) (LBk : list block) (pidk : bptr),
    (k + S r)%nat = length ws ->
    as_VIS H sk1 msF1 = MS R1 F (Z_to_bv 64 MS_HEAD) fc None m1 (seg_rom asegs) -> rfull R1 ->
    mk_regs R1 (w + 4 * Z.of_nat k) (Z.of_nat (S r)) -> as_AKREL H sk1 (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    ms_nz ws k -> ms_mem (ms_pref ws k) sb LBk pidk sk1 m1 ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    induction r as [|r IH]; intros k msF1 mo1 sk1 m1 R1 sb LBk pidk KR VIS1 HF1 RG KR1 MP1 NZ MM.
    - eapply (ms_st3 k 0 msF1 mo1 sk1 m1 R1 sb LBk pidk KR); [| exact VIS1 | exact HF1 | exact RG | exact KR1 | exact MP1 | exact NZ | exact MM].
      intros Hr. exfalso. lia.
    - eapply (ms_st3 k (S r) msF1 mo1 sk1 m1 R1 sb LBk pidk KR); [| exact VIS1 | exact HF1 | exact RG | exact KR1 | exact MP1 | exact NZ | exact MM].
      intros _ msFk mok sk mk Rk sbk LBk' pidk' VISk HFk RGk KRk MPk NZk MMk.
      exact (IH (S k) msFk mok sk mk Rk sbk LBk' pidk' ltac:(lia) VISk HFk RGk KRk MPk NZk MMk).
  Qed.

  Lemma ms_entry : forall (msF : machine_state) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 MKSTR_ENTRY) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 w -> a2 = Z_to_bv 64 nw ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros msF t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv VIS E0 E1 E2 KR ERR.
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold MKSTR_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2, SPL.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    destruct (ms_fsr m RF0) as [FF1 FF2].
    pose proof OBJ as (OC1 & OC2 & OW1 & OW2 & OW3 & OW4).
    assert (NW0 : 0 <= nw < 2 ^ 24) by (unfold nw, Zlen in *; lia).
    assert (PB : 0x6e8000 <= p /\ p + 24 <= 2 ^ 47) by (destruct PBAND; lia).
    assert (SHC : 0x7fff7000 < sh aceil) by (clear - ACF1; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R0 eqn:HR0.
    assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    assert (H10 : getr R0 10 = wz p) by (rewrite HR0, E0; reflexivity).
    assert (H11 : getr R0 11 = wz w) by (rewrite HR0, E1; reflexivity).
    assert (H12 : getr R0 12 = wz nw) by (rewrite HR0, E2; reflexivity).
    assert (H2 : getr R0 2 = wz spz) by (rewrite HR0; exact spz_sp').
    destruct (ms_B1_ok R0 F fc m p w nw spz lo H10 H11 H12 H2 AC0 ST0 ltac:(lia) ltac:(lia) SPH ltac:(lia) W0 ltac:(lia)
                ltac:(unfold nw in *; lia) ms_w_nz)
      as (R1 & M1 & Hms & MU1 & WM1 & FR1 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K18 & K19 & K20 & KK).
    unfold wz in K1, K2, K8, K9, K10, K11, K12, K18, K19, K20.
    pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).

    assert (SWL : aceil <= spz - 80) by lia.
    destruct (stack_window_ok H LB LF (spz - 80) spz SWL FS2) as (SW1 & SW2 & SW3).
    destruct (client_frame H HH s LB LF B [(spz - 80, spz)] m M1 RH0 RF0 AC0 RA0 MU1 WM1
                ltac:(apply Forall_cons; [exact SW1 | apply Forall_nil]) ltac:(apply Forall_cons; [exact SW2 | apply Forall_nil])
                ltac:(apply Forall_cons; [exact SW3 | apply Forall_nil]))
      as (RH1 & RF1 & AC1 & RA1).
    assert (XP1 : xpres H LB spz [] m M1).
    { eapply (xpres_of_munch H s LB spz _ _ m m M1); [exact HH | exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (ST1 : stk asegs M1 lo spz) by (eapply BakeStackRep.stk_high_transport; [exact ST0 | exact WM1 | unfold AIMG_TOP; lia]).
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S00 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. repeat split; lia. }
    assert (ADV1 : addressable M1 p 24).
    { eapply addressable_transport_hi; [exact ADV0 | exact MU1 | exact WM1 | unfold AAPP_HI; lia |].
      apply Forall_cons; [right; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (PW1 : wr_at asegs M1 p 24) by exact (ms_wr_at_wmono _ _ _ _ PWR WM1).
    destruct (ms_wr_at_rw_cells M1 p 24 PW1 ltac:(lia) ltac:(lia)) as (junk & CBJ).
    assert (SV1 : shvis M1 p (p + 24)).
    { destruct PFF as (f & Hf & Q1 & Q2).
      destruct (ah_RFS_range H HH LF M1 RF1) as [AF RR]. destruct (RR f Hf) as (Z0 & Z1 & Z2 & _).
      destruct AF as (G1 & G2 & G3 & G4). unfold AFS_HDR in Z1. unfold AIMG_TOP in G1.
      eapply shvis_sub; [exact (ah_frm_shvis H HH LF M1 f RF1 Hf) | lia | lia | lia | lia | lia]. }
    eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1.

    eapply (ahh_evt_then H HH); [exact KR1 | exact VIS1 | |].
    { eapply (ah_memset H HH) with (c := 0) (junk := junk) (lo := lo); rewrite ?K2, ?K10, ?K11, ?K12, ?u64_of_Z by lia.
      - reflexivity.
      - lia.
      - exact CBJ.
      - eapply addressable_accessible; [exact ADV1 | lia | lia | unfold AAPP_HI; lia].
      - exact SV1.
      - exact (proj1 (stk_split asegs M1 lo (spz - 80) spz ST1 ltac:(lia))).
      - exact LO1.
      - unfold AINTRIN_STACK; lia.
      - exact MI1.
      - exact AC1.
      - lia.
      - unfold in_app_mem, ASHADOW_BASE, AHI_LO, AAPP_HI. unfold AFS_SIZE in *. destruct PBAND; [left | right]; lia.
      - exact OW3.
      - destruct OW4; [left | right]; lia. }
    intros msF2 mo2 KR2 MP2 POST.
    destruct POST as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & CB2 & AC2).
    rewrite K2, K10, K12, !u64_of_Z in MU2 by lia. rewrite K10, K12, !u64_of_Z in CB2 by lia.
    change (Z.to_nat 24) with 24%nat in CB2.
    rewrite K1, (ret_pc_even 0xea6d4 ltac:(lia) eq_refl) in VIS2.
    lazymatch type of VIS2 with _ = MS ?RR _ _ _ _ _ _ => set (R2 := RR) in VIS2 end.
    assert (HF2 : rfull R2) by (unfold R2; apply rfull_mkR).
    assert (KR2R1 : forall r, In r [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R2 r = getr R1 r).
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [reflexivity|]). destruct Hr. }

    assert (SWL2 : aceil <= spz - 80 - AINTRIN_STACK) by (unfold AINTRIN_STACK; lia).
    destruct (stack_window_ok H LB LF (spz - 80 - AINTRIN_STACK) (spz - 80) SWL2 FS2) as (SX1 & SX2 & SX3).
    destruct (client_frame H HH s LB LF B [(p, p + 24); (spz - 80 - AINTRIN_STACK, spz - 80)] M1 m2 RH1 RF1 AC1 RA1 MU2 WM2
                ltac:(apply Forall_cons; [exact OW1 | apply Forall_cons; [exact SX1 | apply Forall_nil]])
                ltac:(apply Forall_cons; [exact OW2 | apply Forall_cons; [exact SX2 | apply Forall_nil]])
                ltac:(apply Forall_cons; [exact OW3 | apply Forall_cons; [exact SX3 | apply Forall_nil]]))
      as (RH2 & RF2 & AC2' & RA2).
    assert (MM0 : ms_mem [] SShort LB 0 s m2).
    { split; [exact MI2|].
      split; [eapply BakeStackRep.stk_high_transport; [exact ST1 | exact WM2 | unfold AIMG_TOP; lia]|].
      split.
      { exists errv. eapply rw_cells_transport; [exact ERR1 | exact MU2 | exact WM2 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
        cbn. unfold ATP, AINTRIN_STACK. repeat split; lia. }
      split; [exact RA2|]. split; [exact AC2'|]. split; [exact RF2|].
      split.
      { eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 |].
        apply Forall_cons; [|apply Forall_cons; [left; cbn [fst]; unfold AHI_LO, AINTRIN_STACK; lia | apply Forall_nil]].
        unfold stack0_ok; cbn [fst snd]. destruct PBAND; [right | left]; unfold AHI_LO; lia. }
      split; [exact RH2|].
      split; [exact (lb_own_wmono _ _ _ (lb_own_wmono _ _ _ OWN WM1) WM2)|].
      split.
      { eapply rw_cells_transport; [rewrite HR0 in FR1; exact FR1 | exact MU2 | exact WM2 |].
        unfold FRAME. rewrite v4_cells_size_map_C8'. cbn [length disjoint_from fst snd]. change (Z.of_nat 10) with 10.
        unfold AINTRIN_STACK. split; [destruct OW4; lia|]. split; [lia | exact I]. }
      split.
      { eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP1 | lia | intros bb Hb; exact Hb | intros a Ha; cbn in Ha; destruct Ha] |].
        eapply (xpres_of_munch H s LB spz _ _ m M1 m2); [exact HH | exact RH0 | exact MU2 | exact WM2 |].
        apply Forall_cons; [right; intros a Ha; left; cbn [fst snd] in *; lia|].
        apply Forall_cons; [left; cbn [fst snd]; unfold AINTRIN_STACK; lia | apply Forall_nil]. }
      split.
      { unfold strA. apply str_nil; [lia | lia | | |].
        - exact (mdef_of_rw_cells_hi m2 p _ CB2 ltac:(unfold AIMG_TOP; lia)).
        - destruct CB2 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
          pose proof (ms_fld0 m2 p 0 HB ltac:(lia)) as K. change (Z.of_nat 0) with 0 in K. rewrite Z.add_0_r in K. exact K.
        - destruct CB2 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
          exact (ms_fld0 m2 p 1 HB ltac:(lia)). }
      split; [exact I|].
      split; [reflexivity|].
      split.
      { eapply addressable_transport_hi; [exact ADV1 | exact MU2 | exact WM2 | unfold AAPP_HI; lia |].
        apply Forall_cons; [destruct PBAND; [left | right]; cbn [fst snd]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO in *; lia|].
        apply Forall_cons; [right; cbn [fst]; unfold AHI_LO, AINTRIN_STACK; lia | apply Forall_nil]. }
      split; [exact (ms_wr_at_wmono _ _ _ _ PW1 WM2)|].
      split; [unfold ms_spent, ms_phi; lia|].
      unfold Zlen; cbn [length]; lia. }

    destruct (ms_B2_ok R2 F fc m2 nw w ltac:(exact K18) ltac:(exact K8) ltac:(unfold nw in *; lia) ltac:(unfold nw in *; lia) W4
                ltac:(intros Hn; apply ms_w_nz; unfold nw in *; lia)) as (R3 & HZ & HN).
    assert (MP12 : as_MPRES H mo mo2) by (eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]).
    destruct (Z.eq_dec nw 0) as [NZ0|NZ1].
    -
      destruct (HZ NZ0) as [Hms2 KK2].
      pose proof (msteps_full asegs _ _ Hms2 HF2) as HF3. cbn [ms_regs] in HF3.
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms2 |].
      intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
      assert (WS0 : length ws = 0%nat) by (unfold nw, Zlen in NZ0; lia).
      assert (CS0 : @nil Z = ms_chars ws) by (apply length_zero_iff_nil in WS0; rewrite WS0; reflexivity).
      assert (E2' : getr R3 2 = Z_to_bv 64 (spz - 80)) by (rewrite (KK2 2%bv ltac:(inb)), (KR2R1 2%bv ltac:(inb)); exact K2).
      assert (E3' : getr R3 3 = gp) by (rewrite (KK2 3%bv ltac:(inb)), (KR2R1 3%bv ltac:(inb)), (KK 3%bv ltac:(inb)), HR0; reflexivity).
      assert (E4' : getr R3 4 = tp) by (rewrite (KK2 4%bv ltac:(inb)), (KR2R1 4%bv ltac:(inb)), (KK 4%bv ltac:(inb)), HR0; reflexivity).
      assert (E25 : getr R3 25 = s9) by (rewrite (KK2 25%bv ltac:(inb)), (KR2R1 25%bv ltac:(inb)), (KK 25%bv ltac:(inb)), HR0; reflexivity).
      assert (E26 : getr R3 26 = s10) by (rewrite (KK2 26%bv ltac:(inb)), (KR2R1 26%bv ltac:(inb)), (KK 26%bv ltac:(inb)), HR0; reflexivity).
      assert (E27 : getr R3 27 = s11) by (rewrite (KK2 27%bv ltac:(inb)), (KR2R1 27%bv ltac:(inb)), (KK 27%bv ltac:(inb)), HR0; reflexivity).
      eapply (ms_exit msF3 mo3 s m2 R3 [] SShort LB 0 CS0 VIS3 HF3 E2' E3' E4' E25 E26 E27 KR3).
      + eapply (ah_mpres_trans H HH); [exact MP12 | exact MP3].
      + exact MM0.
    -
      destruct (HN NZ1) as (Hms2 & L18 & L21 & L22 & L23 & KK2).
      pose proof (msteps_full asegs _ _ Hms2 HF2) as HF3. cbn [ms_regs] in HF3.
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms2 |].
      intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
      assert (LW : (0 + S (length ws - 1))%nat = length ws) by (unfold nw, Zlen in NZ1; lia).
      eapply (ms_loop (length ws - 1) 0 msF3 mo3 s m2 R3 SShort LB 0 LW VIS3 HF3).
      + replace (w + 4 * Z.of_nat 0) with w by lia.
        replace (Z.of_nat (S (length ws - 1))) with nw by (unfold nw, Zlen in *; lia).
        split; [rewrite (KK2 2%bv ltac:(inb)), (KR2R1 2%bv ltac:(inb)); exact K2|].
        split; [rewrite (KK2 3%bv ltac:(inb)), (KR2R1 3%bv ltac:(inb)), (KK 3%bv ltac:(inb)), HR0; reflexivity|].
        split; [rewrite (KK2 4%bv ltac:(inb)), (KR2R1 4%bv ltac:(inb)), (KK 4%bv ltac:(inb)), HR0; reflexivity|].
        split; [rewrite (KK2 8%bv ltac:(inb)), (KR2R1 8%bv ltac:(inb)); exact K8|].
        split; [rewrite L18, (KR2R1 8%bv ltac:(inb)); exact K8|].
        split; [rewrite (KK2 9%bv ltac:(inb)), (KR2R1 9%bv ltac:(inb)); exact K9|].
        split; [rewrite (KK2 20%bv ltac:(inb)), (KR2R1 20%bv ltac:(inb)); exact K20|].
        split; [rewrite (KK2 19%bv ltac:(inb)), (KR2R1 19%bv ltac:(inb)); exact K19|].
        split; [rewrite L21; reflexivity|]. split; [rewrite L22; reflexivity|]. split; [rewrite L23; reflexivity|].
        split; [rewrite (KK2 25%bv ltac:(inb)), (KR2R1 25%bv ltac:(inb)), (KK 25%bv ltac:(inb)), HR0; reflexivity|].
        split; [rewrite (KK2 26%bv ltac:(inb)), (KR2R1 26%bv ltac:(inb)), (KK 26%bv ltac:(inb)), HR0; reflexivity|].
        rewrite (KK2 27%bv ltac:(inb)), (KR2R1 27%bv ltac:(inb)), (KK 27%bv ltac:(inb)), HR0; reflexivity.
      + exact KR3.
      + eapply (ah_mpres_trans H HH); [exact MP12 | exact MP3].
      + intros i Hi. lia.
      + exact MM0.
  Qed.
End MKP.

Theorem mkstr_ok {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps_bp H -> mkstr_stmtA H.
Proof.
  intros H HHb. unfold mkstr_stmtA.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF
    p w ws lo B shi errv.
  intros VIS E0 E1 E2 NWR WSR W4 W0 WH WK P8 ADV PFF OBJ PBAND PWR OWN RH KR MS1 MS2 MS3 CST TRO RA SPB SP16 SP47 ST CE LOl
    ERR MI TPV AC RF S0 SHI.
  pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
  unfold MKSTR_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK in LOl.
  eapply (ms_entry H HHb ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF p w ws lo B shi (bv_unsigned sp));
    try eassumption; try reflexivity.
  - split; [unfold MKSTR_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK; lia|]. split; [exact SP47 | exact SP16].
  - split; [exact CE | unfold MKSTR_STACK, SPB_STACK, AOPNEW_STACK, AMALLOC_STACK; lia].
Qed.
