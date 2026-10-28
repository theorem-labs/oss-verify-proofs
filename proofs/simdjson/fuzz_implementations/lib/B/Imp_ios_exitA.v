(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv MonadX ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Pj_loc_kit Pj_os_kit.

From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import FX_Layout FX_Stdio_iface FX_Exit Imp_ios_defsA Imp_xifaceA F_uselocaleA Imp_oflushA Imp_syncA Imp_woflushA Imp_wsyncA Imp_wunshiftA.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.

Notation bsegs := ImageA.bsegs.
Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0).
Ltac retpc_lit := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (apply bv_eq; vm_compute; reflexivity) end.

Lemma impl_post_evtA : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  impl bsegs (at_node bsegs) t Q ms -> (forall r ms', Q r ms' -> evt bsegs (Q' r) ms') ->
  impl bsegs (at_node bsegs) t Q' ms.
Proof.
  induction t as [r|n k IH|kc IHc]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
  - destruct H as [z H]. exists z. eapply IHc; eauto.
Qed.
Lemma implM_post_evtA : forall {St A} (c : M St A) s Q Q' ms,
  implM bsegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt bsegs (Q' a s') ms') ->
  implM bsegs c s Q' ms.
Proof.
  intros St A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evtA; [exact H|].
  intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.

Notation COUT := 0x6bc718%Z (only parsing).    Notation CLOG := 0x6bc998%Z (only parsing).
Notation WCOUT := 0x6bc7b8%Z (only parsing).   Notation WCLOG := 0x6bca38%Z (only parsing).
Notation SBCOUT := 0x6bc4c8%Z (only parsing).  Notation SBCERR := 0x6bc528%Z (only parsing).
Notation SBWCOUT := 0x6bc588%Z (only parsing). Notation SBWCERR := 0x6bc5e8%Z (only parsing).
Notation VO_C := 0x17d5d8%Z (only parsing).    Notation VSB_C := 0x17da38%Z (only parsing).
Notation VO_W := 0x17d6f8%Z (only parsing).    Notation VSB_W := 0x17db68%Z (only parsing).
Notation FF16 := (Z_to_bv 8 16) (only parsing).

Definition iosx_img_facts (m : mem) : Prop :=
  rw_cells bsegs m 0x17d5c0 [C8 (Z_to_bv 64 8)]
  /\ rw_cells bsegs m 0x17d6e0 [C8 (Z_to_bv 64 8)]
  /\ rw_cells bsegs m 0x17da68 [C8 (Z_to_bv 64 0x1226b8)]
  /\ rw_cells bsegs m 0x17db98 [C8 (Z_to_bv 64 0x122e1c)]
  /\ rw_cells bsegs m 0x17de28 [C8 (Z_to_bv 64 0x14a7c8)]
  /\ rw_cells bsegs m 0x17e0d8 [C8 (Z_to_bv 64 0x149ffc)].

Definition ios_views (m : mem) : Prop :=
     (ostream_cells COUT VO_C 8 SBCOUT VSB_C F_SYNC m FF16 /\ sbuf_cells SBCOUT RSTDOUT LOC_CVC VT_CVC UNSH_C (IOS + 12) m)
  /\ (ostream_cells CLOG VO_C 8 SBCERR VSB_C F_SYNC m FF16 /\ sbuf_cells SBCERR RSTDERR LOC_CVC VT_CVC UNSH_C (IOS + 20) m)
  /\ (wostream_cells WCOUT VO_W 8 SBWCOUT VSB_W F_WSYNC m FF16 /\ wsbuf_cells SBWCOUT RSTDOUT LOC_CVW VT_CVW WUNSH (IOS + 36) m)
  /\ (wostream_cells WCLOG VO_W 8 SBWCERR VSB_W F_WSYNC m FF16 /\ wsbuf_cells SBWCERR RSTDERR LOC_CVW VT_CVW WUNSH (IOS + 44) m).

Ltac tk H n nm := lazymatch type of H with rw_cells _ _ ?A ?cs => let A2 := eval cbv in (A + Z.of_nat (cells_size (firstn n cs)))%Z in take H n A2 nm end.
Ltac drop H n := let J := fresh "J" in tk H n J; clear J.

Ltac retypeU H cs' := apply (fun X => rw_cells_retype _ _ _ _ cs' X) in H;
  [| cbn [cells_wf cell_wf]; repeat split; try apply repeat_length; reflexivity | apply bytes_eq_unsigned; vm_compute; reflexivity | reflexivity].
Ltac ffbyte H := retypeU H [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 16); CB 6 (repeat (Z_to_bv 8 0) 6)]; drop H 1%nat; let T := fresh "V" in tk H 1%nat T; clear H; rename T into H.
Ltac rdhalf H := retypeU H [C4 z64; C4 z64]; let T := fresh "V" in tk H 1%nat T; clear H; rename T into H.

Ltac ostream_views H V FF RD SB TIE := tk H 1%nat V; drop H 1%nat; tk H 1%nat FF; ffbyte FF; drop H 2%nat; tk H 1%nat RD; rdhalf RD; tk H 1%nat SB; drop H 11%nat; tk H 1%nat TIE; drop H 1%nat.

Ltac sbuf_views H V F3 := tk H 1%nat V; drop H 7%nat; tk H 3%nat F3; drop H 1%nat.

Lemma ios_views_of : forall m, ios_block m -> iosx_img_facts m -> locx3 m -> ios_views m.
Proof.
  intros m H (G1 & G2 & G3 & G4 & G5 & G6) (L1 & L2 & L3). unfold ios_block, ios_cells, IOS in H.
  drop H 8%nat.
  sbuf_views H CV CF. sbuf_views H EV EF. sbuf_views H WV WF. sbuf_views H WEV WEF.
  drop H 26%nat.
  ostream_views H OV OFF ORD OSB OTIE.
  ostream_views H WOV WOFF WORD WOSB WOTIE.
  drop H 40%nat.
  ostream_views H LV LFF LRD LSB LTIE.
  ostream_views H WLV WLFF WLRD WLSB WLTIE.
  clear H. unfold ios_views, ostream_cells, sbuf_cells, wostream_cells, wsbuf_cells, IOS, LOC_CVC, LOC_CVW, VT_CVC, VT_CVW, UNSH_C, WUNSH, F_SYNC, F_WSYNC.
  unfold LOC_CVC, LOC_CVW, VT_CVC, VT_CVW in L1, L2, L3.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma ook_c : forall O SB lo, 0 < O -> O + 152 <= GLOBALS_TOP -> 0 < SB -> SB + 8 <= GLOBALS_TOP -> GLOBALS_TOP <= lo -> ostream_ok O VO_C 8 SB VSB_C F_SYNC lo FF16.
Proof. intros O SB lo A B C D E. unfold ostream_ok, F_SYNC, GLOBALS_TOP in *. repeat split; try lia; vm_compute; reflexivity. Qed.
Lemma ook_w : forall O SB lo, 0 < O -> O + 152 <= GLOBALS_TOP -> 0 < SB -> SB + 8 <= GLOBALS_TOP -> GLOBALS_TOP <= lo -> wostream_ok O VO_W 8 SB VSB_W F_WSYNC lo FF16.
Proof. intros O SB lo A B C D E. unfold wostream_ok, F_WSYNC, GLOBALS_TOP in *. repeat split; try lia; vm_compute; reflexivity. Qed.
Lemma sbok_c : forall SB Fp STP lo, 0 < SB -> SB + 88 <= GLOBALS_TOP -> 0 <= Fp < 2^64 -> 0 <= STP < 2^64 -> GLOBALS_TOP <= lo -> sbuf_ok SB Fp LOC_CVC VT_CVC UNSH_C STP lo.
Proof. intros SB Fp STP lo A B C D E. unfold sbuf_ok, LOC_CVC, VT_CVC, UNSH_C, GLOBALS_TOP in *. repeat split; try lia; vm_compute; reflexivity. Qed.
Lemma sbok_w : forall SB Fp STP lo, 0 < SB -> SB + 88 <= GLOBALS_TOP -> 0 <= Fp < 2^64 -> 0 <= STP < 2^64 -> GLOBALS_TOP <= lo -> wsbuf_ok SB Fp LOC_CVW VT_CVW WUNSH STP lo.
Proof. intros SB Fp STP lo A B C D E. unfold wsbuf_ok, LOC_CVW, VT_CVW, WUNSH, GLOBALS_TOP in *. repeat split; try lia; vm_compute; reflexivity. Qed.

Lemma land_sub : forall f m k, Z.land f m = 0 -> Z.land m k = k -> Z.land f k = 0.
Proof. intros f m k H E. rewrite <- E, Z.land_assoc, H. apply Z.land_0_l. Qed.

Ltac drop_bundles :=
  repeat match goal with
  | H : ostream_cells _ _ _ _ _ _ _ _ |- _ => clear H | H : sbuf_cells _ _ _ _ _ _ _ |- _ => clear H
  | H : wostream_cells _ _ _ _ _ _ _ _ |- _ => clear H | H : wsbuf_cells _ _ _ _ _ _ _ |- _ => clear H end.

Ltac name_stk ST := first [ match goal with H : stk _ _ _ _ |- _ => tryif constr_eq H ST then fail else (try clear ST; rename H into ST) end | idtac ].
Ltac name_mi MI := match goal with H : mem_inv _ _ |- _ => rename H into MI end.

Ltac name_file FC := match goal with H : rw_cells _ _ _ (file_cells _ _ _ _ _ _ _ _ _ _ _) |- _ => unfold file_cells in H; rename H into FC end.
Ltac after_call ST MI := drop_bundles; name_stk ST; name_mi MI; try retpc_lit.

Section IosExitA.
  Variable IX : mem -> Prop.
  Variable XLO : Z.
  Hypothesis IXF : IX_frame_stmt IX XLO.
  Hypothesis IFW : ifwrite0_stmt IX XLO.
  Hypothesis IFFI : ifflush_idle_stmt IX XLO.
  Hypothesis IWC : iwcrtomb_stmt IX XLO.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis IFFS : ifflush_stdout_stmt IX XLO get_so set_so.

  Ltac ix_now IXm MU WM lo hi :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "IXc" in
      assert (H : IX mm) by (eapply (IXF _ lo hi); [exact IXm | exact MU | exact WM | unfold GLOBALS_TOP; lia | unfold sub_fp, XWI, XTPLOC; cbn [outside]; intros; lia])
    | |- implM _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "IXc" in
      assert (H : IX mm) by (eapply (IXF _ lo hi); [exact IXm | exact MU | exact WM | unfold GLOBALS_TOP; lia | unfold sub_fp, XWI, XTPLOC; cbn [outside]; intros; lia])
    end.

Definition cflush_post (O Fp : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (flags : word) (wfn bufp bufsize fd lbf : Z) (tail : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 O) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' Fp (file_cells flags 0 0 0 wfn bufp bufsize fd mode' lbf tail)
    /\ IX m'.

Lemma clog_flush : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo hi : Z) (flags mode : word) (wend e : Z) (tail : list byte),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4736) -> (GLOBALS_TOP <= lo) -> (XLO <= lo) -> (bv_unsigned sp < 2^63) ->
  ios_block m -> iosx_img_facts m -> locx3 m ->
  rw_cells bsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x6dec00 0 2 mode 0xffffffff tail) ->
  Z.land (bv_unsigned flags) 40 = 0 -> (wend = 0 \/ (wend = 0x6dec00 /\ e = 0x6dec00)) -> (0 <= e < 2^63) ->
  (bv_unsigned sp <= hi) -> IX m ->
  mem_inv bsegs m ->
  evt bsegs (cflush_post CLOG RSTDERR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags F_STDIO_WRITE 0x6dec00 0 2 0xffffffff tail lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CLOG) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_OFLUSH) fc None m (seg_rom bsegs)).
Proof.
  intros until tail. intros ST LO GLO XL SPHI IOSB IMGF LX3 FC FL40 WCASE EB HHI IXm MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold GLOBALS_TOP in *. unfold file_cells in FC.
  pose proof (ios_views_of m IOSB IMGF LX3) as (_ & [OC SBC] & _). clear IOSB IMGF LX3.
  destruct OC as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8). destruct SBC as (B1 & B2 & B3). unfold IOS, LOC_CVC, VT_CVC, UNSH_C, F_SYNC in O8, B1, B2, B3.
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

  call (oflush_seg1 CLOG VO_C 8 SBCERR VSB_C F_SYNC lo);
    [ exact ST | lia | unfold GLOBALS_TOP; lia | exact (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 (conj O6 (conj O7 O8))))))) | apply ook_c; unfold GLOBALS_TOP; lia | exact MI | ].
  after_call ST MI. match goal with H : rw_cells _ _ _ (oflush_frame _ _ _ _ _ _) |- _ => rename H into FRO end.

  name_sp sp (-48)%Z. replace (bv_unsigned sp + -48) with (bv_unsigned sp0) in ST, FRO by lia.
  call (sync_seg1a SBCERR RSTDERR LOC_CVC VT_CVC UNSH_C (IOS + 20) lo);
    [ exact ST | lia | unfold GLOBALS_TOP; lia | exact (conj B1 (conj B2 B3)) | apply sbok_c; unfold GLOBALS_TOP, IOS; lia | exact MI | ].
  after_call ST MI.
  match goal with H : rw_cells _ _ (bv_unsigned sp0 + -80) [CB 8 _] |- _ => rename H into J0 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp0 + -72) [CB 8 _] |- _ => rename H into JE end.
  match goal with H : rw_cells _ _ (bv_unsigned sp0 + -64) [CB 8 _] |- _ => rename H into JB end.
  match goal with H : rw_cells _ _ (bv_unsigned sp0 + -56) (sync_saved _ _ _ _ _ _ _) |- _ => rename H into SAVED end.

  lazymatch type of JE with rw_cells _ _ _ [CB 8 ?j1] => call (unshift_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (bv_unsigned sp0 + -72) (bv_unsigned sp0 + -64) j1) end;
    [ exact JE | reflexivity | reflexivity | lia | lia | lia | exact MI | ].
  after_call ST MI. match goal with H : rw_cells _ _ (bv_unsigned sp0 + -72) [C8 _] |- _ => rename H into JE end.

  call (sync_seg1b SBCERR RSTDERR LOC_CVC VT_CVC UNSH_C (IOS + 20) lo);
    [ lia | lia | exact JE | exact (conj B1 (conj B2 B3)) | apply sbok_c; unfold GLOBALS_TOP, IOS; lia | exact MI | ].
  after_call ST MI. match goal with H : rw_cells _ _ (bv_unsigned sp0 + -72) [C8 _] |- _ => rename H into JE end.

  ix_now IXm MU WM lo hi.
  call_sp (IFW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ RSTDERR _ flags mode wend e e F_STDIO_WRITE 0x6dec00 0 2 0xffffffff tail lo);
    [ exact FC
    | destruct WCASE as [-> | [-> ->]]; [left; split; [reflexivity| apply (land_sub _ 40 8 FL40); reflexivity] | right; lia]
    | right; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | right; reflexivity
    | lia | lia | lia | lia | lia | lia | lia | exact ST | unfold ICPT_DEPTH; lia | unfold GLOBALS_TOP; lia | lia | lia | exact IXc | exact MI | ].
  clear IXc. try match goal with H : IX _ |- _ => clear H end.
  after_call ST MI. try clear FC. name_file FC.
  replace (if wend =? 0 then 0x6dec00 else e) with 0x6dec00%Z in FC by (destruct WCASE as [-> | [-> ->]]; reflexivity).

  call (sync_seg2 SBCERR RSTDERR LOC_CVC VT_CVC UNSH_C (IOS + 20) lo 3);
    [ left; reflexivity | exact (conj B1 (conj B2 B3)) | apply sbok_c; unfold GLOBALS_TOP, IOS; lia | exact MI | ].
  after_call ST MI.

  ix_now IXm MU WM lo hi.
  call_sp (IFFI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ RSTDERR flags _ _ _ F_STDIO_WRITE 0x6dec00 0 2 0xffffffff tail lo);
    [ exact FC | reflexivity | right; reflexivity | lia | lia | lia | exact ST | unfold ICPT_DEPTH; lia | unfold GLOBALS_TOP; lia | lia | lia | exact IXc | exact MI | ].
  clear IXc. try match goal with H : IX _ |- _ => clear H end.
  after_call ST MI. try clear FC. name_file FC.

  call (sync_seg3 lo); [ exact ST | lia | unfold GLOBALS_TOP; lia | exact J0 | exact JE | exact JB | exact SAVED | exact MI | ].
  after_call ST MI. clear J0 JE JB SAVED.
  unname_sp.

  call (oflush_seg2 CLOG VO_C 8 SBCERR VSB_C F_SYNC lo);
    [ exact ST | lia | unfold GLOBALS_TOP; lia | exact FRO | exact (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 (conj O6 (conj O7 O8))))))) | apply ook_c; unfold GLOBALS_TOP; lia | exact MI | ].
  after_call ST MI.
  ix_now IXm MU WM lo hi.
  apply evt_done. unfold cflush_post. do 14 eexists. eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FC| exact IXc].
Qed.

Section WFlush.

  Variables (O SB STP Fp BUFP BSZ FD : Z).
  Definition wnb : Prop := 0x17e1a0 <= Fp /\ Fp + 232 <= 0x6bc488 /\ 0x6bc488 <= SB /\ SB + 96 <= O /\ O + 152 <= 0x6bcc28 /\ 0x6bc488 <= STP /\ STP + 8 <= 0x6bcc28 /\ (Fp = RSTDOUT \/ Fp = RSTDERR)
                        /\ 0 <= BUFP /\ 0 <= BSZ /\ 0 < BUFP + BSZ /\ BUFP + BSZ <= GLOBALS_TOP /\ Fp + 232 <= BUFP.
  Hypothesis NB : wnb.

  Definition wflush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (flags : word) (wfn lbf : Z) (tail : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 O) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (0x6be3b8, 0x6be3b8 + 8)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' Fp (file_cells flags 0 0 0 wfn BUFP BSZ FD mode' lbf tail)
      /\ rw_cells bsegs m' 0x6be3b8 [C8 (Z_to_bv 64 0x6de6b0)]
      /\ IX m'.

  Lemma wflush : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo hi : Z) (flags mode : word) (wfn lbf : Z) (tail : list byte),
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4800) -> (GLOBALS_TOP <= lo) -> (XLO <= lo) -> (bv_unsigned sp < 2^63) -> (bv_unsigned sp <= hi) ->
    wostream_cells O VO_W 8 SB VSB_W F_WSYNC m FF16 -> wsbuf_cells SB Fp LOC_CVW VT_CVW WUNSH STP m -> rw_cells bsegs m (LOC_CVW + 16) [C8 (Z_to_bv 64 0x37998)] ->
    rw_cells bsegs m STP [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m Fp (file_cells flags 0 0 0 wfn BUFP BSZ FD mode lbf tail) -> Z.land (bv_unsigned flags) 8 = 0 -> (lbf = 10 \/ lbf = 0xffffffff) ->
    tp = Z_to_bv 64 0x6be3e8 -> rw_cells bsegs m 0x6be3b8 [C8 (Z_to_bv 64 0x6de6b0)] ->
    IX m -> mem_inv bsegs m ->
    evt bsegs (wflush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags wfn lbf tail lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 O) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 F_WOFLUSH) fc None m (seg_rom bsegs)).
  Proof.
    intros until tail; intros ST LO GLO XL SPHI HHI OC SBC CVL STC FC FL8 LBF TPE TPL IXm MI.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof NB as (F0 & F1 & F2 & F3 & F4 & F5 & F5b & F5c & F6 & F7 & F8 & F9 & F10).
    unfold GLOBALS_TOP in *. unfold file_cells in FC. unfold LOC_CVW in CVL.
    destruct OC as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8). destruct SBC as (B1 & B2 & B3). unfold LOC_CVW, VT_CVW, WUNSH, F_WSYNC in O8, B1, B2, B3.
    pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232); (0x6be3b8, 0x6be3b8 + 8)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

    call (woflush_seg1 O VO_W 8 SB VSB_W F_WSYNC lo);
      [ exact ST | lia | unfold GLOBALS_TOP; lia | exact (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 (conj O6 (conj O7 O8))))))) | apply ook_w; unfold GLOBALS_TOP; lia | exact MI | ].
    after_call ST MI. match goal with H : rw_cells _ _ _ (woflush_frame _ _ _ _ _ _) |- _ => rename H into FRO end.

    name_sp sp (-48)%Z. replace (bv_unsigned sp + -48) with (bv_unsigned sp0) in ST, FRO by lia.
    call (wsync_seg1a SB Fp LOC_CVW VT_CVW WUNSH STP lo);
      [ exact ST | lia | unfold GLOBALS_TOP; lia | exact (conj B1 (conj B2 B3)) | apply sbok_w; unfold GLOBALS_TOP; lia | exact MI | ].
    after_call ST MI.
    match goal with H : rw_cells _ _ (bv_unsigned sp0 + -80) [CB 8 _] |- _ => rename H into J0 end.
    match goal with H : rw_cells _ _ (bv_unsigned sp0 + -72) [CB 8 _] |- _ => rename H into JE end.
    match goal with H : rw_cells _ _ (bv_unsigned sp0 + -64) [CB 8 _] |- _ => rename H into JB end.
    match goal with H : rw_cells _ _ (bv_unsigned sp0 + -56) (wsync_saved _ _ _ _ _ _ _) |- _ => rename H into SAVED end.

    name_sp sp0 (-80)%Z. replace (bv_unsigned sp0 + -80) with (bv_unsigned sp1) in ST by lia. replace (bv_unsigned sp0 + -72) with (bv_unsigned sp1 + 8) in JE by lia.
    ix_now IXm MU WM lo hi.
    lazymatch type of JE with rw_cells _ _ _ [CB 8 ?j1] =>
      call (wunshift_spec IX XLO IXF IWC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ LOC_CVW (bv_unsigned sp1 + 8) (bv_unsigned sp1 + 16) STP lo hi j1) end;
      [ reflexivity | exact CVL | unfold LOC_CVW; lia | unfold LOC_CVW, GLOBALS_TOP; lia | f_equal; lia | f_equal; lia | f_equal; lia | exact JE | lia | lia | lia | lia | lia
      | reflexivity | exact STC | lia | unfold XTPLOC; lia
      | exact TPE | exact TPL | exact ST | unfold WUNSH_DEPTH, ICPT_DEPTH; lia | unfold GLOBALS_TOP; lia | lia | lia | exact IXc | exact MI | ].
    clear IXc. try match goal with H : IX _ |- _ => clear H end.
    after_call ST MI. try clear JE. try clear TPL.
    match goal with H : rw_cells _ _ (bv_unsigned sp1 + 8) [C8 _] |- _ => rename H into JE end.
    match goal with H : rw_cells _ _ 0x6be3b8 _ |- _ => rename H into TPL end.
    unname_sp. replace (bv_unsigned sp0 + -80 + 8) with (bv_unsigned sp0 + -72) in JE by lia. replace (bv_unsigned sp0 + -80 + 16) with (bv_unsigned sp0 + -64) in JE by lia.

    call (wsync_seg1b SB Fp LOC_CVW VT_CVW WUNSH STP lo);
      [ lia | lia | exact JE | exact (conj B1 (conj B2 B3)) | apply sbok_w; unfold GLOBALS_TOP; lia | exact MI | ].
    after_call ST MI. match goal with H : rw_cells _ _ (bv_unsigned sp0 + -72) [C8 _] |- _ => rename H into JE end.

    ix_now IXm MU WM lo hi.
    call_sp (IFW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fp _ flags mode 0 0 0 wfn BUFP BSZ FD lbf tail lo);
      [ exact FC | left; split; [reflexivity| exact FL8] | exact LBF | reflexivity | reflexivity | reflexivity | reflexivity | exact F5c
      | lia | lia | lia | lia | lia | lia | lia | exact ST | unfold ICPT_DEPTH; lia | unfold GLOBALS_TOP; lia | lia | lia | exact IXc | exact MI | ].
    clear IXc. try match goal with H : IX _ |- _ => clear H end.
    after_call ST MI. try clear FC. name_file FC. cbn [Z.eqb] in FC.

    call (wsync_seg2 SB Fp LOC_CVW VT_CVW WUNSH STP lo 0);
      [ right; reflexivity | exact (conj B1 (conj B2 B3)) | apply sbok_w; unfold GLOBALS_TOP; lia | exact MI | ].
    after_call ST MI.

    ix_now IXm MU WM lo hi.
    call_sp (IFFI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fp flags _ _ _ wfn BUFP BSZ FD lbf tail lo);
      [ exact FC | reflexivity | exact F5c | lia | lia | lia | exact ST | unfold ICPT_DEPTH; lia | unfold GLOBALS_TOP; lia | lia | lia | exact IXc | exact MI | ].
    clear IXc. try match goal with H : IX _ |- _ => clear H end.
    after_call ST MI. try clear FC. name_file FC.

    call (wsync_seg3 lo); [ exact ST | lia | unfold GLOBALS_TOP; lia | exact J0 | exact JE | exact JB | exact SAVED | exact MI | ].
    after_call ST MI. clear J0 JE JB SAVED.
    unname_sp.

    call (woflush_seg2 O VO_W 8 SB VSB_W F_WSYNC lo);
      [ exact ST | lia | unfold GLOBALS_TOP; lia | exact FRO | exact (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 (conj O6 (conj O7 O8))))))) | apply ook_w; unfold GLOBALS_TOP; lia | exact MI | ].
    after_call ST MI.
    ix_now IXm MU WM lo hi.
    apply evt_done. unfold wflush_post. do 14 eexists. eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FC| split; [exact TPL| exact IXc]].
  Qed.
End WFlush.
Lemma wnb_wcout : wnb WCOUT SBWCOUT (IOS + 36) RSTDOUT RSTDOUT_BUF 1024.
Proof. unfold wnb, IOS, GLOBALS_TOP. lia. Qed.
Lemma wnb_wclog : wnb WCLOG SBWCERR (IOS + 44) RSTDERR 0x6dec00 0.
Proof. unfold wnb, IOS, GLOBALS_TOP. lia. Qed.

Definition cout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (flags : word) (tail : list byte) (lo : Z) (canary : word) (m : mem) (s : St) : unit -> St -> machine_state -> Prop :=
  fun _ s' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem) (so' : stdout_st),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 COUT) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ so' = (if 0 <? zlength (so_buf (get_so s)) then so_after (get_so s) else get_so s) /\ s' = set_so so' s
    /\ rw_cells bsegs m' RSTDOUT (file_cells flags 0 0 0 (wfn_of so') RSTDOUT_BUF 1024 1 mode' (lbf_of so') tail)
    /\ ssp_cells m' canary
    /\ IX m'.

Lemma cout_flush : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo hi : Z) (s : St) (flags mode : word) (tail bufbytes : list byte) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 4736) -> (GLOBALS_TOP <= lo) -> (XLO <= lo) -> (bv_unsigned sp < 2^63) -> (bv_unsigned sp <= hi) ->
  ios_block m -> iosx_img_facts m -> locx3 m ->
  rw_cells bsegs m RSTDOUT (file_cells flags (if so_active (get_so s) then RSTDOUT_BUF + 1024 else 0) (if so_active (get_so s) then RSTDOUT_BUF + zlength (so_buf (get_so s)) else 0)
                                       (if so_active (get_so s) then RSTDOUT_BUF else 0) (wfn_of (get_so s)) RSTDOUT_BUF 1024 1 mode (lbf_of (get_so s)) tail) ->
  Z.land (bv_unsigned flags) 72 = 0 ->
  rw_cells bsegs m RSTDOUT_BUF [CB 1024 bufbytes] -> firstn (length (so_buf (get_so s))) bufbytes = to_bytes (so_buf (get_so s)) -> (zlength (so_buf (get_so s)) <= 1024) ->
  (so_active (get_so s) = false -> so_buf (get_so s) = []) ->
  ssp_cells m canary -> IX m ->
  mem_inv bsegs m ->
  implM bsegs (stdout_exit_flush get_so set_so) s (cout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags tail lo canary m s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 COUT) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 F_OFLUSH) fc None m (seg_rom bsegs)).
Proof.
  intros until canary. intros ST LO GLO XL SPHI HHI IOSB IMGF LX3 FC FL72 BUF BUFP BUFL INACT SSP IXm MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold GLOBALS_TOP in *. unfold file_cells in FC.
  pose proof (ios_views_of m IOSB IMGF LX3) as ([OC SBC] & _). clear IOSB IMGF LX3.
  destruct OC as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8). destruct SBC as (B1 & B2 & B3). unfold IOS, LOC_CVC, VT_CVC, UNSH_C, F_SYNC in O8, B1, B2, B3.
  destruct SSP as [SG SC]. unfold got_ssp, ssp_guard in SG, SC.
  assert (ZL0 : 0 <= zlength (so_buf (get_so s))) by (unfold zlength; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  eapply (implM_evt bsegs). 2:{ intros ms' H; exact H. } cbv beta.

  call (oflush_seg1 COUT VO_C 8 SBCOUT VSB_C F_SYNC lo);
    [ exact ST | lia | unfold GLOBALS_TOP; lia | exact (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 (conj O6 (conj O7 O8))))))) | apply ook_c; unfold GLOBALS_TOP; lia | exact MI | ].
  after_call ST MI. match goal with H : rw_cells _ _ _ (oflush_frame _ _ _ _ _ _) |- _ => rename H into FRO end.

  name_sp sp (-48)%Z. replace (bv_unsigned sp + -48) with (bv_unsigned sp0) in ST, FRO by lia.
  call (sync_seg1a SBCOUT RSTDOUT LOC_CVC VT_CVC UNSH_C (IOS + 12) lo);
    [ exact ST | lia | unfold GLOBALS_TOP; lia | exact (conj B1 (conj B2 B3)) | apply sbok_c; unfold GLOBALS_TOP, IOS; lia | exact MI | ].
  after_call ST MI.
  match goal with H : rw_cells _ _ (bv_unsigned sp0 + -80) [CB 8 _] |- _ => rename H into J0 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp0 + -72) [CB 8 _] |- _ => rename H into JE end.
  match goal with H : rw_cells _ _ (bv_unsigned sp0 + -64) [CB 8 _] |- _ => rename H into JB end.
  match goal with H : rw_cells _ _ (bv_unsigned sp0 + -56) (sync_saved _ _ _ _ _ _ _) |- _ => rename H into SAVED end.

  lazymatch type of JE with rw_cells _ _ _ [CB 8 ?j1] => call (unshift_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (bv_unsigned sp0 + -72) (bv_unsigned sp0 + -64) j1) end;
    [ exact JE | reflexivity | reflexivity | lia | lia | lia | exact MI | ].
  after_call ST MI. match goal with H : rw_cells _ _ (bv_unsigned sp0 + -72) [C8 _] |- _ => rename H into JE end.

  call (sync_seg1b SBCOUT RSTDOUT LOC_CVC VT_CVC UNSH_C (IOS + 12) lo);
    [ lia | lia | exact JE | exact (conj B1 (conj B2 B3)) | apply sbok_c; unfold GLOBALS_TOP, IOS; lia | exact MI | ].
  after_call ST MI. match goal with H : rw_cells _ _ (bv_unsigned sp0 + -72) [C8 _] |- _ => rename H into JE end.

  ix_now IXm MU WM lo hi.
  call_sp (IFW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ RSTDOUT _ flags mode _ _ _ (wfn_of (get_so s)) RSTDOUT_BUF 1024 1 (lbf_of (get_so s)) tail lo);
    [ exact FC
    | destruct (so_active (get_so s)); [right; lia | left; split; [reflexivity| apply (land_sub _ 72 8 FL72); reflexivity]]
    | unfold lbf_of; destruct (so_lbf_nl (get_so s)); [left | right]; reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | left; reflexivity
    | lia | lia | lia | lia | lia | lia | lia | exact ST | unfold ICPT_DEPTH; lia | unfold GLOBALS_TOP; lia | lia | lia | exact IXc | exact MI | ].
  clear IXc. try match goal with H : IX _ |- _ => clear H end.
  after_call ST MI. try clear FC. name_file FC.
  replace (if (if so_active (get_so s) then RSTDOUT_BUF + 1024 else 0) =? 0 then RSTDOUT_BUF else (if so_active (get_so s) then RSTDOUT_BUF + zlength (so_buf (get_so s)) else 0))%Z
     with (RSTDOUT_BUF + zlength (so_buf (get_so s)))%Z in FC
     by (destruct (so_active (get_so s)); [reflexivity | rewrite (INACT eq_refl); reflexivity]).

  call (sync_seg2 SBCOUT RSTDOUT LOC_CVC VT_CVC UNSH_C (IOS + 12) lo 3);
    [ left; reflexivity | exact (conj B1 (conj B2 B3)) | apply sbok_c; unfold GLOBALS_TOP, IOS; lia | exact MI | ].
  after_call ST MI.
  apply evt_done.

  name_sp sp0 (-80)%Z. replace (bv_unsigned sp0 + -80) with (bv_unsigned sp1) in ST by lia.
  ix_now IXm MU WM lo hi.
  lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mX _) =>
  lazymatch type of FC with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?md :: _) =>
    eapply implM_post_evtA;
    [ eapply (IFFS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mX s flags md tail bufbytes lo canary);
      [ exact INACT | unfold stdout_cells, file_cells; exact FC | exact FL72 | exact BUF | exact BUFP | exact BUFL | reflexivity
      | exact ST | unfold ICPT_DEPTH; lia | unfold GLOBALS_TOP; lia | lia | lia | split; [exact SG| exact SC] | exact IXc | exact MI ]
    | cbv beta; intros [] s' ms' PO; unfold ifflush_stdout_post in PO; revert ms' PO; post_call bsegs mX ]
  end end.
  clear IXc. try match goal with H : IX _ |- _ => clear H end.
  after_call ST MI. try clear FC. name_file FC.
  match goal with H : ssp_cells _ _ |- _ => clear H end.
  unname_sp.

  call (sync_seg3 lo); [ exact ST | lia | unfold GLOBALS_TOP; lia | exact J0 | exact JE | exact JB | exact SAVED | exact MI | ].
  after_call ST MI. clear J0 JE JB SAVED.
  unname_sp.

  call (oflush_seg2 COUT VO_C 8 SBCOUT VSB_C F_SYNC lo);
    [ exact ST | lia | unfold GLOBALS_TOP; lia | exact FRO | exact (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 (conj O6 (conj O7 O8))))))) | apply ook_c; unfold GLOBALS_TOP; lia | exact MI | ].
  after_call ST MI.
  ix_now IXm MU WM lo hi.
  apply evt_done. unfold cout_post. do 14 eexists. eexists. eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [eassumption|]. split; [eassumption|]. split; [exact FC| split; [split; [exact SG| exact SC]| exact IXc]].
Qed.

Lemma mbstates_of_block : forall m, ios_block m -> rw_cells bsegs m (IOS + 36) [C8 z64] /\ rw_cells bsegs m (IOS + 44) [C8 z64].
Proof.
  intros m H. unfold ios_block, ios_cells, IOS in H.
  drop H 4%nat. tk H 3%nat W3. clear H. retypeU W3 [C4 z64; C8 z64; C8 z64; C4 z64].
  drop W3 1%nat. tk W3 1%nat M1. tk W3 1%nat M2. unfold IOS. split; [exact M1| exact M2].
Qed.

Definition X_IOSDTOR_A : Z := 0x12213c.
Definition HDXA : Z := 4864.

Definition ios_exitA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (canary : word) (m : mem) (s : St)
    : unit -> St -> machine_state -> Prop :=
  fun _ s' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (so' : stdout_st) (flags eflags mode1 mode2 : word) (tail etail : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (XWI lo (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ so' = (if 0 <? zlength (so_buf (get_so s)) then so_after (get_so s) else get_so s) /\ s' = set_so so' s
    /\ rw_cells bsegs m' RSTDOUT (file_cells flags 0 0 0 (wfn_of so') RSTDOUT_BUF 1024 1 mode1 (lbf_of so') tail) /\ Z.land (bv_unsigned flags) 72 = 0
    /\ rw_cells bsegs m' RSTDERR (file_cells eflags 0 0 0 F_STDIO_WRITE 0x6dec00 0 2 mode2 0xffffffff etail) /\ Z.land (bv_unsigned eflags) 40 = 0
    /\ rw_cells bsegs m' XTPLOC [C8 (Z_to_bv 64 0x6de6b0)] /\ ssp_cells m' canary /\ ios_block m' /\ IX m'.

Definition ios_exitA_stmt : Prop :=
  forall (lo : Z) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : St) (canary : word),
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - HDXA) -> (GLOBALS_TOP <= lo) -> (XLO <= lo) -> tp = Z_to_bv 64 0x6be3e8 ->
    ios_block m -> iosx_img_facts m -> locx3 m -> rw_cells bsegs m XTPLOC [C8 (Z_to_bv 64 0x6de6b0)] ->
    stdout_file m (get_so s) -> stderr_wfile0 m -> ssp_cells m canary -> IX m -> mem_inv bsegs m ->
    implM bsegs (stdout_exit_flush get_so set_so) s (ios_exitA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m s)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IOS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 X_IOSDTOR_A) fc None m (seg_rom bsegs)).

Theorem ios_exitA_proof : ios_exitA_stmt.
Proof.
  intros lo ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s canary ST LO GLO XL TPE IOSB IMGF LX3 TPL SOF SEF SSP IXm MI.
  destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
  destruct SEF as (eflags & emode & e & wend & etail & EFC & EFL40 & ECASE & EB).
  destruct SSP as [SG SC]. unfold got_ssp, ssp_guard in SG, SC. unfold file_cells in FC, EFC. unfold XTPLOC in TPL.
  pose proof (mbstates_of_block m IOSB) as [STW STE]. unfold IOS in STW, STE.
  unfold ios_block, ios_cells, IOS in IOSB.
  destruct LX3 as (L1 & L2 & L3). unfold LOC_CVC, LOC_CVW, VT_CVC, VT_CVW, CLOC in L1, L2, L3. destruct IMGF as (G1 & G2 & G3 & G4 & G5 & G6).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold HDXA, X_IOSDTOR_A, GLOBALS_TOP in *.
  pose proof (stk_below _ _ _ _ MI ST ltac:(lia)) as SPU. unfold UTOP in SPU.
  pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDERR, RSTDERR + 232); (0x6be3b8, 0x6be3b8 + 8)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  eapply (implM_evt bsegs). 2:{ intros ms' H; exact H. } cbv beta.
  carve_frame 16%nat ST.
  lstep. lstep. lstep.
  lstep. lstep.
  lstep. lstep.
  apply evt_done.

  name_sp sp (-16)%Z. replace (bv_unsigned sp + -16) with (bv_unsigned sp0) in ST by lia.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => rename H into FR end.
  ix_now IXm MU WM lo (bv_unsigned sp). clear IXm. rename IXc into IXm.
  lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mX _) =>
    eapply implM_post_evtA;
    [ eapply (cout_flush _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mX lo (bv_unsigned sp) s flags mode tail bufbytes canary);
      [ exact ST | lia | unfold GLOBALS_TOP; lia | lia | lia | lia | exact IOSB | exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 G6))))) | exact (conj L1 (conj L2 L3))
      | exact FC | exact FL72 | exact BUF | exact BUFP | exact BUFL | exact INACT | split; [exact SG| exact SC] | exact IXm | exact MI ]
    | cbv beta; intros [] s' ms' PO; unfold cout_post in PO; revert ms' PO; post_call bsegs mX ]
  end.
  after_call ST MI. try clear FC. try clear BUF. clear IXm. name_file FC. match goal with H : ssp_cells _ _ |- _ => clear H end.
  match goal with H : IX _ |- _ => rename H into IX1 end.

  lstep. lstep.
  call (clog_flush _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (bv_unsigned sp) eflags emode wend e etail);
    [ exact ST | lia | unfold GLOBALS_TOP; lia | lia | lia | exact IOSB | exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 G6))))) | exact (conj L1 (conj L2 L3))
    | exact EFC | exact EFL40 | exact ECASE | exact EB | lia | exact IX1 | exact MI | ].
  after_call ST MI. try clear EFC. clear IX1. match goal with H : rw_cells _ _ RSTDERR (file_cells _ _ _ _ _ _ _ _ _ _ _) |- _ => unfold file_cells in H; rename H into EFC end.
  match goal with H : IX _ |- _ => rename H into IX2 end.

  lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => pose proof (ios_views_of mX IOSB (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 G6))))) (conj L1 (conj L2 L3))) as (_ & _ & [WOC WSB] & _) end.
  lazymatch type of FC with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?md :: _) =>
  call (wflush WCOUT SBWCOUT (IOS + 36) RSTDOUT RSTDOUT_BUF 1024 1 wnb_wcout _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (bv_unsigned sp) flags md _ _ tail) end;
    [ exact ST | lia | unfold GLOBALS_TOP; lia | lia | lia | lia | exact WOC | exact WSB | exact L3 | exact STW
    | exact FC | apply (land_sub _ 72 8 FL72); reflexivity | unfold lbf_of; destruct (so_lbf_nl _); [left| right]; reflexivity | exact TPE | exact TPL | exact IX2 | exact MI | ].
  after_call ST MI. try clear FC. try clear TPL. clear IX2. name_file FC. match goal with H : rw_cells _ _ 0x6be3b8 _ |- _ => rename H into TPL end.
  match goal with H : IX _ |- _ => rename H into IX3 end.

  lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => pose proof (ios_views_of mX IOSB (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 G6))))) (conj L1 (conj L2 L3))) as (_ & _ & _ & [WLC WLSB]) end.
  lazymatch type of EFC with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C4 ?md :: _) =>
  call (wflush WCLOG SBWCERR (IOS + 44) RSTDERR 0x6dec00 0 2 wnb_wclog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (bv_unsigned sp) eflags md _ _ etail) end;
    [ exact ST | lia | unfold GLOBALS_TOP; lia | lia | lia | lia | exact WLC | exact WLSB | exact L3 | exact STE
    | exact EFC | apply (land_sub _ 40 8 EFL40); reflexivity | right; reflexivity | exact TPE | exact TPL | exact IX3 | exact MI | ].
  after_call ST MI. try clear EFC. try clear TPL. clear IX3.
  match goal with H : rw_cells _ _ RSTDERR (file_cells _ _ _ _ _ _ _ _ _ _ _) |- _ => rename H into EFC end.
  match goal with H : rw_cells _ _ 0x6be3b8 _ |- _ => rename H into TPL end.
  match goal with H : IX _ |- _ => rename H into IX4 end.

  unname_sp.
  lstep. lstep. lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  try retpc_lit.
  apply evt_done. unfold ios_exitA_post, XWI, XTPLOC. do 15 eexists. eexists. eexists. exists flags, eflags. do 2 eexists. exists tail, etail. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [eassumption|]. split; [eassumption|].
  split; [exact FC|]. split; [exact FL72|]. split; [exact EFC|]. split; [exact EFL40|]. split; [exact TPL|]. split; [split; [exact SG| exact SC]|].
  split; [unfold ios_block, ios_cells, IOS; exact IOSB| exact IX4].
Qed.
End IosExitA.
