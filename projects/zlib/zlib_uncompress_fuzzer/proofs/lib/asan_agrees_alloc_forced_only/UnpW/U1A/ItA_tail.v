(* reloc-zl14c *)
(* [U14] inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import ItA_base ItA_ldefs ItA_switch ItA_here ItA_fill ItA_cnt2 ItA_sub ItA_loop.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

  (* [U14] the 1.3.1 register homes of ALL moved to 1.4 by tools/regmap_text_gr.py (t0>a7 t1>t2 t2>t1 a7>t0) *)
Lemma entry_bytes_lit : forall hb, 0 <= hb < 256 ->
  cells_bytes [C1 (Z_to_bv 8 64); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 hb))); C2 (Z_to_bv 64 0)]
  = le4 (Z_to_bv 64 (code_pack 64 hb 0)).
Proof. intros hb H. exact (entry_bytes 64 hb 0 ltac:(lia) H ltac:(lia)). Qed.
Lemma entry_bytes_lit1 :
  cells_bytes [C1 (Z_to_bv 8 64); C1 (Z_to_bv 8 1); C2 (Z_to_bv 64 0)] = le4 (Z_to_bv 64 (code_pack 64 1 0)).
Proof. exact (entry_bytes 64 1 0 ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

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
  Notation MST := (mst SP SPA S F PB LP gp tp FR fc rt mx).
  Notation MINV := (fun m st => minv SPA S F PB m1 m ty rt nx bits lf w1 st).
  Notation SPU := (spure work1Ar rt nx).
  Notation RET r wfx cfx nxt bts := (ret_pre SP SPA S F PB LP gp tp FR fc m1 r lf wfx cfx nxt bts).

  (* [comment removed for export] *)
  Definition fin_tbl (st : ItSt) : arr :=
    if negb (t_huff st =? 0) then arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0) else t_tbl st.

  (* [comment removed for export] *)
  Lemma it_setret : forall (st : ItSt) (t : arr) (m : amem) (v0 v96 v104 v112 : word) (of : Z -> Z)
      (x1 x6 x7 x10 x11 x17 x25 x28 x29 : word) (x14 x24 : word),
    itb_inv SPA S F PB m1 m v0 (Z_to_bv 64 (isD ty)) (Z_to_bv 64 (isL ty)) (Z_to_bv 64 (Z.shiftr (S + 160) 3 + 2147450880))
            (Z_to_bv 64 (t_used st)) (Z_to_bv 64 (EXA ty S)) (Z_to_bv 64 (BSA ty S)) (Z_to_bv 64 (2 ^ rt - 1))   (* [P14] 1.4: extra in slot 40, base in 48 *)
            (Z_to_bv 64 (lowS (t_low st))) (Z_to_bv 64 (it_match ty)) (Z_to_bv 64 (2 ^ t_curr st)) (Z_to_bv 64 (S + 160))
            v96 v104 v112 (arr_get (t_count st)) of lf w1 (arr_get t) (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
    0 <= t_used st < 65536 -> 0 <= nx ->
    evtF asegs RNG (RET 0 w1 (arr_get t) (Z_to_bv 64 (S + 1384 + 4 * (nx + t_used st))) (Z_to_bv 64 rt))
      (bst SP SPA S F PB LP gp tp FR fc x1 x17 x7 x6 x10 x11 (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880))
           (Z_to_bv 64 rt) x14 (Z_to_bv 64 (t_len st)) (Z_to_bv 64 (t_used st)) (Z_to_bv 64 (t_drop st)) x24 x25 x28 x29
           (Z_to_bv 64 (S + 1384 + 4 * t_next st)) (Z_to_bv 64 (t_sym st)) 0x96314 m).
  Proof using All.
    (* [P14] 1.4's setret (0x962dc .. 0x9630c) reads used from a6 (loaded at 0x96280), so it has
       no ld a1,32(s1), and it falls through to 0x96310 with no j: 13 instructions, 1.3.1 had 15 *)
    intros until x24. intros INV Fused Hnx. open_ctx CX. open_inv INV. unfold bst.
    zs. zs. zs.               (* ld a0,24(s1) / lbu / bnez *)
    zs. zs.                   (* ld a4,88(s1) / ld a0,0(a4) *)
    zs. zs. setreg 11 (Z_to_bv 64 (4 * t_used st)) ltac:(rewrite zext32_x4 by lia; reflexivity).
    zs. setreg 10 (Z_to_bv 64 (S + 1384 + 4 * (nx + t_used st))) ltac:(f_equal; lia).
    zs.                       (* sd a0,0(a4) *)
    zs. zs. zs. zs.           (* lb a0,0(a2) / bnez / li a0,0 / sw a3,0(s3) *)
    apply evtF_done. unfold ret_pre. eexists. do 17 eexists. do 15 eexists. exists (arr_get (t_count st)), of.
    split; [reflexivity|]. unfold itb_inv, itb_W, frm15. do 10 (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma it_tail : forall (st : ItSt) (m : amem) (v0 v96 v104 v112 : word) (of : Z -> Z)
      (x1 x6 x10 x11 x16 x17 x25 x29 : word),
    MINV m st v0 v96 v104 v112 of -> SPU st ->
    0 <= t_len st - t_drop st <= 15 -> 0 <= t_used st < 65536 -> 0 <= t_huff st < 81920 ->   (* [P14] 65536 + 16384; the mover's 81908 was an address move *)
    (t_huff st <> 0 -> 0 <= t_next st + t_huff st < 1444) ->
    evtF asegs RNG (RET 0 w1 (arr_get (fin_tbl st)) (Z_to_bv 64 (S + 1384 + 4 * (nx + t_used st))) (Z_to_bv 64 rt))
      (* [U14] 1.4 keeps the constant 1 in s9 (1.3.1: t3) *)
      (* [P14] 1.4 enters at 0x96280, where it loads used into a6 (ld a6,32(s1)) before the beqz;
         1.3.1 loaded it into a1 inside setret *)
      (MST st x1 x6 (Z_to_bv 64 (t_len st - t_drop st)) x10 x11 x16 x17 (Z_to_bv 64 1) x25 x29 0x962b8 m).
  Proof using All.
    intros until x29. intros INV HP Fhb Fused Fhuff Ffin.
    pose proof C as C'. open_itc C'. open_spure HP.
    pose proof INV as INV0. open_ctx CX. unfold minv in INV. open_inv INV. unfold mst, bst.
    zs.
    zs. zbr0 KH.
    - (* [comment removed for export] *)
      eapply evtF_mono; [eapply (it_setret st (t_tbl st) m v0 v96 v104 v112 of); [exact INV0 | exact Fused | lia]|].
      cbv beta. intros ms' HR. unfold fin_tbl. replace (t_huff st =? 0) with true by (symmetry; apply Z.eqb_eq; exact KH). exact HR.
    - specialize (Ffin KH).
      zs. zs. setreg 10 (Z_to_bv 64 (4 * t_huff st)) ltac:(rewrite zext32_x4 by lia; reflexivity).
      zs. setreg 10 (Z_to_bv 64 (S + 1384 + 4 * (t_next st + t_huff st))) ltac:(f_equal; lia).
      f32_open_at CDS (t_next st + t_huff st) D ED CH CC.
      do 4 zs. zs. zs. zs.               (* [comment removed for export] *)
      do 4 zs. zs.                       (* [comment removed for export] *)
      zs. do 4 zs. zs.                   (* [comment removed for export] *)
      f32_close_at CH CC ED (code_pack 64 (t_len st - t_drop st) 0) CDS; [apply entry_bytes_lit; lia|]. subst D.
      assert (HIDX : 0 <= t_next st + t_huff st < arr_len (t_tbl st)) by (rewrite TL; lia).
      apply (fun H => f32arr_ext asegs _ _ _ _ (arr_get (fin_tbl st)) H
                        (fun j _ => eq_trans (fupd_arr_set (t_tbl st) _ _ j HIDX)
                                             (f_equal (fun a => arr_get a j) (eq_sym (ltac:(unfold fin_tbl; replace (t_huff st =? 0) with false by (symmetry; apply Z.eqb_neq; exact KH); reflexivity)
                                                                                   : fin_tbl st = arr_set (t_tbl st) (t_next st + t_huff st) (code_pack 64 (t_len st - t_drop st) 0)))))) in CDS.
      eapply (it_setret st (fin_tbl st)); [| exact Fused | lia].
      unfold itb_inv, itb_W, frm15. do 10 (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition tbl0 : arr := arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) (nx + 1) (code_pack 64 1 0).

  Lemma it_max0 : forall (m : amem) (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v96 v104 v112 : word) (cnt of : Z -> Z) (bitsw : word)
      (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word),
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 (Z_to_bv 64 (S + 160)) v96 v104 v112
            cnt of lf wf cf (Z_to_bv 64 (S + 1384 + 4 * nx)) bitsw ->
    evtF asegs RNG (RET 0 wf (arr_get tbl0) (Z_to_bv 64 (S + 1384 + 4 * (nx + 2))) (Z_to_bv 64 1))
      (bst SP SPA S F PB LP gp tp FR fc x1 x17 x7 x6 x10 x11 (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880)) x13 x14 x15 x16 x5 x24 x25 x28 x29 x30 x31 0x964d0 m).
  Proof using All.
    intros until x31. intros INV. pose proof C as C'. open_itc C'.
    assert (ROOM : nx + 2 <= 1444) by (clear - Hroom Hnx; unfold it_room, ENOUGH_LENS, ENOUGH_DISTS in Hroom; destruct ty; lia).
    open_ctx CX. open_inv INV. unfold bst.
    do 5 zs. do 4 zs.
    apply (fun H => f32arr_ext asegs _ _ _ _ (arr_get (tblA cf)) H (fun j _ => eq_sym (tblA_get cf j))) in CDS.
    f32_open_at CDS nx D ED CH CC.   (* [P14] a worker: restored; the draft had these two lines' words scrambled *)
    do 4 zs. do 3 zs. do 4 zs. do 3 zs. do 4 zs.
    zs. zs. zs.                        (* [comment removed for export] *)
    f32_close_at CH CC ED (code_pack 64 1 0) CDS; [apply entry_bytes_lit1|]. subst D.
    assert (HI1 : 0 <= nx < arr_len (tblA cf)) by (unfold tblA; rewrite arr_len_init; cbv [IDefs.N_CODES]; lia).
    apply (fun H => f32arr_ext asegs _ _ _ _ (arr_get (arr_set (tblA cf) nx (code_pack 64 1 0))) H
                      (fun j _ => fupd_arr_set (tblA cf) _ _ j HI1)) in CDS.
    zs. zs.                            (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (S + 1384 + 4 * (nx + 1))) ltac:(f_equal; lia).
    f32_open_at CDS (nx + 1) D ED CH CC.
    do 4 zs. do 3 zs. do 4 zs. do 3 zs. do 4 zs. zs.
    f32_close_at CH CC ED (code_pack 64 1 0) CDS; [apply entry_bytes_lit1|]. subst D.
    assert (HI2 : 0 <= nx + 1 < arr_len (arr_set (tblA cf) nx (code_pack 64 1 0))) by (rewrite arr_len_set; unfold tblA; rewrite arr_len_init; cbv [IDefs.N_CODES]; lia).
    apply (fun H => f32arr_ext asegs _ _ _ _ (arr_get tbl0) H
                      (fun j _ => fupd_arr_set (arr_set (tblA cf) nx (code_pack 64 1 0)) _ _ j HI2)) in CDS.
    zs. zs. zs. zs.                    (* [P14] lb / beqz -> 0x96308 / li a0,0 / sw: 1.4 falls through to 0x96310 (1.3.1 had a j) *)
    apply evtF_done. unfold ret_pre. eexists. do 17 eexists. do 15 eexists. exists cnt, of.
    split; [reflexivity|]. unfold itb_inv, itb_W, frm15.
    replace (S + 1384 + 4 * (nx + 2)) with (S + 1384 + 4 * nx + 8) by lia.
    do 10 (split; [eassumption|]). eassumption.
  Qed.
End P.
End CANSEC1.
