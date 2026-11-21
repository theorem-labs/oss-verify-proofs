(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure UbFit2 ItBGlue.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import ItBTac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import ItB_base ItB_ldefs ItB_switch ItB_here ItB_fill ItB_cnt2 ItB_sub ItB_loop.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Lemma zext32_shift32 : forall x, 0 <= x < 4294967296 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia). apply Z.div_mul. lia.
Qed.
Lemma zext32_shift30' : forall x, 0 <= x < 4294967296 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 30 = 4 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (4 * 2 ^ 30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma lor_hb64 : forall hb, 0 <= hb < 256 -> Z.lor (Z.shiftl hb 8) 64 = code_pack 64 hb 0.
Proof.
  intros hb H. rewrite <- (lor_code_pack 64 hb 0) by lia. change (Z.shiftl 0 16) with 0. rewrite Z.lor_0_l. apply Z.lor_comm.
Qed.
Lemma entry_halves_320 : cells_bytes [C2 (Z_to_bv 64 320); C2 (Z_to_bv 64 0)] = le4 (Z_to_bv 64 (code_pack 64 1 0)).
Proof. exact (entry_halves 320 ltac:(lia)). Qed.

Ltac close_inv_e := unfold itb_inv, itb_W, frm19; do 10 (split; [eassumption|]); eassumption.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP SPA S F PB top : Z) (m1 : amem).
  Variables (ty : codetype) (lf wf cf : Z -> Z) (lo codes nx bits : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis C : itc ty lf lo codes nx bits cf wf.

  Notation LP := (S + 168 + 2 * lo).
  Notation cntAr := (cntA lf lo codes).
  Notation mx := (mxA lf lo codes).
  Notation mn := (mnA lf lo codes).
  Notation rt := (rootA lf lo codes bits).
  Notation work1Ar := (work1A lf lo codes wf).
  Notation w1 := (arr_get (work1A lf lo codes wf)).
  Notation X := (itm_ctx ty (lensA lf) lo nx rt mx).
  Notation BST := (bst SP SPA S F PB LP (cty ty) gp tp FR fc).
  Notation MINV := (fun m st => minv SPA S F PB m1 m ty rt nx bits lf w1 st).
  Notation SHPB := (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880)).
  Notation SPU := (spure work1Ar rt nx).
  Notation RET r wfx cfx nxt bts := (ret_pre SP SPA S F PB LP (cty ty) gp tp FR fc m1 r lf wfx cfx nxt bts).

  (* [comment removed for export] *)
  Definition fin_tbl (st : ItSt) : arr :=
    if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0) else t_tbl st.

  (* [comment removed for export] *)
  Lemma it_setret : forall (used : Z) (t : Z -> Z) (m : amem) (v0 v8 v16 v32 v48 v56 v64 v72 v80 v88 v96 v104 v112 v128 v136 v144 : word)
      (cnt of : Z -> Z) (x1 x5 x6 x7 x10 x11 x12 x15 x16 x17 x25 x28 x29 x30 x31 : word),
    itb_inv SPA S F PB m1 m v0 v8 v16 (Z_to_bv 64 (Z.shiftr (S + 160) 3 + 2147450880)) v32 (Z_to_bv 64 used) v48 v56 v64 v72 v80 v88 v96 v104 v112
            (Z_to_bv 64 (S + 160)) v128 v136 v144 cnt of lf w1 t (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
    0 <= used < 65536 -> 0 <= nx <= 1444 ->
    evtF bsegs RNG (RET 0 w1 t (Z_to_bv 64 (S + 1384 + 4 * (nx + used))) (Z_to_bv 64 rt))
      (BST x1 x5 x6 x7 x10 x11 x12 SHPB (Z_to_bv 64 rt) x15 x16 x17 x25 x28 x29 x30 x31 0x97700 m).
  Proof using All.
    intros until x31. intros INV Fused Hnx. open_ctx CX. open_inv INV. unfold bst.
    zs. zs. zs.               (* [comment removed for export] *)
    zs. zs.                   (* [comment removed for export] *)
    zs. zs.                   (* [comment removed for export] *)
    zs. setreg 12 (Z_to_bv 64 (4 * used)) ltac:(rewrite zext32_shift30' by lia; reflexivity).
    zs. zs. ubg.              (* [comment removed for export] *)
    zs. snez1 15. zs. seqz0 12. zs. zs.
    zs. zs. zs.               (* [comment removed for export] *)
    zs. setreg 11 (Z_to_bv 64 used) ltac:(rewrite Z.mod_small by lia; reflexivity).
    zs. zs. setreg 10 (Z_to_bv 64 (S + 1384 + 4 * (nx + used))) ltac:(rewrite shl2_4x; f_equal; lia).
    zs. zs.                   (* [comment removed for export] *)
    zs. zs. zs. zs.           (* [comment removed for export] *)
    apply evtF_done. unfold ret_pre. eexists. do 16 eexists. do 19 eexists. exists cnt, of.
    split; [reflexivity|]. close_inv_e.
  Qed.

  (* [comment removed for export] *)
  Lemma it_tail : forall (st : ItSt) (m : amem) (v0 v8 v16 v128 v136 : word) (of : Z -> Z)
      (x5 x6 x7 x10 x11 x12 x16 x17 x25 x29 x30 x31 : word),
    MINV m st v0 v8 v16 (Z_to_bv 64 (Z.shiftl (t_len st - t_drop st) 8)) v128 v136 of -> SPU st ->
    (* [U14B] A2 2026-11-12: 81920 = 65536 + 16384 as at 1.3.1 (the mover had moved the bound as an address, to 81908) *)
    0 <= t_len st - t_drop st <= 15 -> 0 <= t_used st < 65536 -> 0 <= t_huff st < 81920 ->
    (t_huff st <> 0 -> 0 <= t_next st + t_huff st < 1444) ->
    evtF bsegs RNG (RET 0 w1 (arr_get (fin_tbl st)) (Z_to_bv 64 (S + 1384 + 4 * (nx + t_used st))) (Z_to_bv 64 rt))
      (* [U14B] A2 2026-11-12: huff is in t4 (x29) at 1.4 (0x9763c beqz t4; 1.3.1 t3 = x28), as break_post in ItB_loop *)
      (BST (Z_to_bv 64 (S + 1384 + 4 * t_next st)) x5 x6 x7 x10 x11 x12 SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) x16 x17 x25
           x29 (Z_to_bv 64 (t_huff st)) x30 x31 0x976a0 m).
  Proof using All.
    intros until x31. intros INV HP Fhb Fused Fhuff Ffin.
    pose proof C as C'. open_itc C'. open_spure HP.
    assert (ROOM : nx <= 1444) by (clear - Hroom Hnx; unfold it_room, ENOUGH_LENS, ENOUGH_DISTS in Hroom; destruct ty; lia).
    pose proof INV as INV0. open_ctx CX. unfold minv in INV. open_inv INV. unfold bst.
    zs. zbr0 KH.
    - (* [comment removed for export] *)
      eapply evtF_mono; [eapply (it_setret (t_used st) (arr_get (t_tbl st)) m); [exact INV0 | exact Fused | lia]|].
      cbv beta. intros ms' HR. unfold fin_tbl. replace (t_huff st =? 0) with true by (symmetry; apply Z.eqb_eq; exact KH). exact HR.
    - specialize (Ffin KH).
      set (hb := t_len st - t_drop st) in *.
      pose proof (code_pack_range 64 hb 0) as HR. change (2 ^ 32) with 4294967296 in HR.
      pose proof (lor_hb64 hb ltac:(lia)) as EHW.
      set (HW := code_pack 64 hb 0) in *.
      zs. ubg.
      zs. zs. setreg 10 (Z_to_bv 64 (4 * t_huff st)) ltac:(rewrite zext32_shift30' by lia; reflexivity).
      zs. zs. ubg. zs. ubg.
      zs. setreg 10 (Z_to_bv 64 (t_huff st)) ltac:(rewrite Z.mod_small by lia; reflexivity).
      zs. zs. setreg 10 (Z_to_bv 64 (S + 1384 + 4 * (t_next st + t_huff st))) ltac:(rewrite shl2_4x; f_equal; lia).
      f32_open_at CDS (t_next st + t_huff st) D ED CH CC.
      do 4 zs. zs. do 4 zs.              (* [comment removed for export] *)
      zs. zs. setreg 11 (Z_to_bv 64 HW) ltac:(rewrite (Z.mod_small (Z.shiftl hb 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia); rewrite EHW; reflexivity).
      zs. zs. zs.                        (* [comment removed for export] *)
      f32_close_at CH CC ED HW CDS; [apply entry_halves; exact HR|]. subst D.
      assert (HIDX : 0 <= t_next st + t_huff st < arr_len (t_tbl st)) by (rewrite TL; lia).
      apply (fun H => f32arr_ext bsegs _ _ _ _ (arr_get (fin_tbl st)) H
                        (fun j _ => eq_trans (fupd_arr_set (t_tbl st) _ _ j HIDX)
                                             (f_equal (fun a => arr_get a j) (eq_sym (ltac:(unfold fin_tbl; replace (t_huff st =? 0) with false by (symmetry; apply Z.eqb_neq; exact KH); reflexivity)
                                                                                   : fin_tbl st = arr_set (t_tbl st) (t_next st + t_huff st) HW))))) in CDS.
      eapply (it_setret (t_used st) (arr_get (fin_tbl st))); [| exact Fused | lia].
      close_inv_e.
  Qed.

  (* [comment removed for export] *)
  Definition tbl0 : arr := arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0).

  Lemma it_max0 : forall (m : amem) (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v128 v136 v144 : word) (cnt of : Z -> Z) (bitsw : word)
      (x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 (Z_to_bv 64 (S + 160)) v128 v136 v144
            cnt of lf wf cf (Z_to_bv 64 (S + 1384 + 4 * nx)) bitsw ->
    evtF bsegs RNG (RET 0 wf (arr_get tbl0) (Z_to_bv 64 (S + 1384 + 4 * (nx + 2))) (Z_to_bv 64 1))
      (BST x1 x5 x6 x7 x10 x11 x12 SHPB x14 x15 x16 x17 x25 x28 x29 x30 x31 0x978f0 m).
  Proof using All.
    intros until x31. intros INV. pose proof C as C'. open_itc C'.
    assert (ROOM : nx + 2 <= 1444) by (clear - Hroom Hnx; unfold it_room, ENOUGH_LENS, ENOUGH_DISTS in Hroom; destruct ty; lia).
    open_ctx CX. open_inv INV. unfold bst.
    zs. zs. zs. zs. zs.               (* [comment removed for export] *)
    zs. zs.                           (* [comment removed for export] *)
    zs. zs. zs. ubg.                  (* [comment removed for export] *)
    zs. zs.                           (* [comment removed for export] *)
    zs. zs.                           (* [comment removed for export] *)
    apply (fun H => f32arr_ext bsegs _ _ _ _ (arr_get (tblA cf)) H (fun j _ => eq_sym (tblA_get cf j))) in CDS.
    f32_open_at CDS nx D ED CH CC.
    do 4 zs. zs. do 4 zs.             (* [comment removed for export] *)
    zs. zs. zs.                       (* [comment removed for export] *)
    f32_close_at CH CC ED (code_pack 64 1 0) CDS; [apply entry_halves_320|]. subst D.
    assert (HI1 : 0 <= nx < arr_len (tblA cf)) by (unfold tblA; rewrite arr_len_init; cbv [IDefs.N_CODES]; lia).
    apply (fun H => f32arr_ext bsegs _ _ _ _ (arr_get (arr_set (tblA cf) nx (code_pack 64 1 0))) H
                      (fun j _ => fupd_arr_set (tblA cf) _ _ j HI1)) in CDS.
    zs. zs.                           (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (S + 1384 + 4 * (nx + 1))) ltac:(f_equal; lia).
    zs. zs. zs. ubg.                  (* [comment removed for export] *)
    zs. zs.                           (* [comment removed for export] *)
    zs. zs.                           (* [comment removed for export] *)
    f32_open_at CDS (nx + 1) D ED CH CC.
    do 4 zs. zs. do 4 zs.
    zs. zs. zs.                       (* [comment removed for export] *)
    f32_close_at CH CC ED (code_pack 64 1 0) CDS; [apply entry_halves_320|]. subst D.
    assert (HI2 : 0 <= nx + 1 < arr_len (arr_set (tblA cf) nx (code_pack 64 1 0))) by (rewrite arr_len_set; unfold tblA; rewrite arr_len_init; cbv [IDefs.N_CODES]; lia).
    apply (fun H => f32arr_ext bsegs _ _ _ _ (arr_get tbl0) H
                      (fun j _ => fupd_arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) _ _ j HI2)) in CDS.
    zs. zs. zs. zs. zs.               (* [comment removed for export] *)
    apply evtF_done. unfold ret_pre. eexists. do 16 eexists. do 19 eexists. exists cnt, of.
    split; [reflexivity|]. unfold itb_inv, itb_W, frm19.
    replace (S + 1384 + 4 * (nx + 2)) with (S + 1384 + 4 * (nx + 1) + 4) by lia.
    do 10 (split; [eassumption|]). eassumption.
  Qed.
End P.
End CANSEC1.
