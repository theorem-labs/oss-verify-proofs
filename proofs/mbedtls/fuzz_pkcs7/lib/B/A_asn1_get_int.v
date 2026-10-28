(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_len P_asn1_get_int.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_len A_asn1_get_int_loops LxConv_getlen LxConv_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.


Local Ltac lx_colZ t ::= lxu_colZ t.
Local Ltac lx_reZ t ::= lxu_reZ t.

Tactic Notation "lxc_apply" uconstr(L) :=
  first [ (eapply L; first [lx_is_mem_goal; eassumption | lazymatch goal with |- @eq (bv _) _ _ => reflexivity end | idtac])
        | (eapply evtA_eq; [ apply lx_MS_regs | eapply L; first [lx_is_mem_goal; eassumption | lazymatch goal with |- @eq (bv _) _ _ => reflexivity end | idtac] ]) ];
  try lx_regs_eq; try lx_app.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP VALP P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= VALP \/ VALP + 4 <= PP.
  Hypothesis D2 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : Z.of_nat (length bs) = 0 \/ VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis VALB : 0 <= VALP /\ VALP + 4 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : VALP mod 4 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < VALP.
  Hypothesis SPL : lo <= bv_unsigned sp - 64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : VALP + 4 <= lo \/ bv_unsigned sp <= VALP.
  Hypothesis DS3 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.

  Notation W := [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - 64, bv_unsigned sp)].
  Notation POST := (asn1_get_int_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m).


  Local Ltac2 Set LiaOrc.tbl := fun () => "00U0@L10878941549.127L11955549567.130L173945366.84   L17807771876.81 L17873211871.82 L21556459630.81 L23888180367.98 L26703880884.84 L28576966805.2  L30240083531.84 L3746526749.129 L3896787041.130 L40834635493.129L40834635493.130L40834635493.83 L40834635493.84 L40967902890.127L4203851315.131 L43180878653.84 L48627689226.129L48627689226.130L48627689226.83 L48627689226.84 L49550767767.84 L49870368978.84 L55259532008.84 L55508994005.2  L59310614641.84 L59314873579.2  L59314873579.3  L59314873579.4  L59314873579.5  L59314988138.1  L59314988138.82 L65470029188.84 L67360715135.130L7172452140.84  00001N01d02E03303S04307B07b07c08D08_09<0;20;30;40;50<S0<i0=P0?60?70?80?90@10@S0A50A60A70A80A90A:0A;0A<0A=0AV0Al0BFS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS31k3cur1i2Hk3HP22HE3SPR3H11S2sp2PP4VALP2bs1k1i2HkS2sp2PP4VALP3END2bs1k3cur1i2Hk2HES2sp2PP4VALP3END2bs3PPB4VALB1k3cur1i2Hk2HE3SPRS2sp2PP4VALP1P2bs1k3cur1i2Hk3HP2S2sp2PP4VALP1P2bs1k3cur1i2Hk3HP2S2AL2CS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB4BUF03NZ13NZ23SPL3LO03DS13DS23DS33cur1i3val3rra3rt23ra03ra23ra33rt33rt43rt53rt62mm2Hk2Hi3HP22HES2sp2PP4VALP1P2bs1k3cur1i2Hk3HP2FS2sp2PP4VALP3BUF2bs1k3cur1i2Hk2HiS2sp2PP4VALP2bs1k1i1c2Hk2HcS2sp2PP4VALP2bs1k1i2Hk2Hi3H11S2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS31k3cur3val1c2Hk3HP22HE2Hc4Hinv3SPR3Hc43H153H163H17FFFS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS31k3cur1i2Hk3HP22HE3SPR3H11S2sp2PP4VALP2bs1k1i2HkS2sp2PP4VALP2bs3PPB4VALB1k1i2Hk3SPR3H11S2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS31k3cur3val1c2Hk3HP22HE2Hc4Hinv3SPRFFFS2sp2PP4VALP2bs3PPB4VALB1k1i3val1c2Hk2Hc3Hv03SPR3H113LORS2sp2PP4VALP3BUF2bs1k3cur1i2Hk3HBRS2sp2PP4VALP3BUF2bs1k3cur1i2Hk3HBRFFFFFFFFS2sp2PP4VALP2bs1k1i2Hk2HiS2sp2PP4VALP2bs1k1i2HkS2sp2PP4VALP2bs1k1i2Hk3H11".
  Lemma loopB_walk : forall (k : nat) (cur i val c : Z)
      (rra rt2 ra0 ra2 ra3 rt3 rt4 rt5 rt6 vv : word) (mm : mem),
    Z.of_nat k = i -> 1 <= i <= 4 -> P + 2 <= cur -> cur + i <= END ->
    0 <= c <= 255 -> (i <= 3 \/ c <= 127) ->
    0 <= val -> val * 2 ^ (8 * i) < 2 ^ 31 -> val < 2 ^ 23 ->
    ro_cells asegs mm cur [C1 (Z_to_bv 8 c)] ->
    rw_cells asegs mm (bv_unsigned sp + -48) [C8 (Z_to_bv 64 (i - 1)); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mm PP [C8 (Z_to_bv 64 cur)] ->
    rw_cells asegs mm VALP [C4 vv] ->
    stk asegs mm lo (bv_unsigned sp + -48) ->
    ro_cells asegs mm 0x1099f8 [C8 (Z_to_bv 64 (al_sb AL))] ->
    ro_cells asegs mm 0x0f5e50 [C8 (Z_to_bv 64 0x1099f8)] ->
    aobj asegs AL CS mm (bv_unsigned sp + -48) 8 -> aobj asegs AL CS mm BUF (Z.of_nat (length bs)) ->
    aobj asegs AL CS mm VALP 4 -> aobj asegs AL CS mm PP 8 ->
    bytes_at asegs mm BUF bs ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST
      (MS (mkR rra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2)) rt2
               (Z_to_bv 64 PP) (Z_to_bv 64 (al_sb AL)) ra0 (Z_to_bv 64 VALP) ra2 ra3
               (Z_to_bv 64 (al_sb AL + Z.shiftr VALP 3)) (Z_to_bv 64 (i - 2)) (Z_to_bv 64 val)
               (Z_to_bv 64 (Z.land VALP 7 + 3)) (Z_to_bv 64 (al_sb AL + Z.shiftr PP 3)) (Z_to_bv 64 VALP)
               s4 s5 s6 s7 s8 s9 s10 s11 rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 0x099d5c) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros cur i val c rra rt2 ra0 ra2 ra3 rt3 rt4 rt5 rt6 vv mm
      Hk Hi HP2 HE Hc Hc4 Hv0 Hinv Hv23 HC HLEN HPPc HVAL ST GSB GOT OLEN OBUF OVAL OPP HBUF MU WM MI; [lia|].
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    lx_hide1 Hinv.
    lx_run_tac (PLAN [0x099d5c] [(0x099d80, DJoin); (0x099d8c, DJoin)] 200%N).
    lx_tree.
    all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x099d5c) _ _ ?mm _] =>
             (match goal with H : bytes_at _ mm BUF bs |- _ =>
                pose proof (ro_byte_of_bytes asegs mm BUF bs (cur + 1) H ltac:(lia) ltac:(lia)) as HB end);
             pose proof (byte_range (nth (Z.to_nat (cur + 1 - BUF)) bs (Z_to_bv 8 0))) as HBR;
             pose proof (lor_256_byte val c Hv0 ltac:(lia)) as LOR;
             unfold lx_hidden in Hinv;
             lxc_apply (IH (cur + 1) (i - 1) (Z.lor (256 * val) c) _)
         | |- _ => idtac
         end.
    all: try lxc_cells_conv.
    all: try (rewrite LOR; assert (Ii : i = 2 \/ i = 3 \/ i = 4) by lia; destruct Ii as [-> | [-> | ->]];
              cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in *; lia).
  Qed.


  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L13119478735.76L13119478735.84L20721071212.84L20721071215.87L20727419499.76L20727419499.84L26604586704.87L26604586707.84L28576966805.2 L32774054100.87L32774054103.84L5093998597.84 L5093998598.87 L52542635763.76L52542635763.84L55508994005.2 L59314988138.1 00000^01L02102V02e03403K03b03c04L04e05S06A07007_07`07cS2sp2PP4VALP1P2bs3PPB4VALB2P03cur3HP04Hcur3SPRS2sp2PP4VALP1P2bs3PPB4VALB2P03cur3HP04Hcur3SPRS2sp2PP4VALP2bs3PPB4VALB3rem4Hrem3SPRS2sp2PP4VALP2bs3PPB4VALB3rem4Hrem3SPRS2sp2PP4VALP2bsS2sp2PP4VALP2bsS2sp2PP4VALP2bs3rem3H16S2sp2PP4VALP2bs3rem3H14FS2sp2PP4VALP2bs3PPB4VALB3rem1c2Hc3SPR3H14S2sp2PP4VALP2bs3rem1c3H14S2sp2PP4VALP1P2bs3PPB4VALB2P03cur3HP04Hcur3SPRS2sp2PP4VALP1P2bs3PPB4VALB2P03cur3HP04Hcur3SPRS2sp2PP4VALP3END2bs3PPB4VALB3cur3rem2HE3SPR3H10S2sp2PP4VALP3END2bs3PPB4VALB3cur3rem2HE3SPR3H14FS1G".
  Lemma exitA_walk : forall (P0 cur rem c : Z)
      (rra rt0 rt1 rt2 ra0 ra2 ra3 ra4 ra5 ra6 ra7 rs2 rt3 rt4 rt5 rt6 valv : word) (mm : mem),
    1 <= rem -> P + 2 <= P0 -> P0 <= cur -> cur + rem <= END -> 0 <= c <= 255 ->
    ra2 = Z_to_bv 64 (-100) -> ra4 = Z_to_bv 64 (cur - P0 + rem) -> ra5 = Z_to_bv 64 (cur - P0) ->
    rs2 = Z_to_bv 64 (al_sb AL + Z.shiftr PP 3) ->
    ro_cells asegs mm cur [C1 (Z_to_bv 8 c)] ->
    rw_cells asegs mm (bv_unsigned sp + -48) [C8 (Z_to_bv 64 rem)] ->
    rw_cells asegs mm PP [C8 (Z_to_bv 64 cur)] ->
    rw_cells asegs mm (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -48) ->
    ro_cells asegs mm 0x1099f8 [C8 (Z_to_bv 64 (al_sb AL))] ->
    ro_cells asegs mm 0x0f5e50 [C8 (Z_to_bv 64 0x1099f8)] ->
    aobj asegs AL CS mm (bv_unsigned sp + -48) 8 -> aobj asegs AL CS mm BUF (Z.of_nat (length bs)) ->
    aobj asegs AL CS mm VALP 4 -> aobj asegs AL CS mm PP 8 ->
    bytes_at asegs mm BUF bs -> rw_cells asegs mm VALP [C4 valv] ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST
      (MS (mkR rra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp rt0 rt1 rt2 (Z_to_bv 64 PP) (Z_to_bv 64 (al_sb AL))
               ra0 (Z_to_bv 64 VALP) ra2 ra3 ra4 ra5 ra6 ra7 rs2 (Z_to_bv 64 VALP) s4 s5 s6 s7 s8 s9 s10 s11
               rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 0x099cd0) fc None mm (seg_rom asegs)).
  Proof.
    intros P0 cur rem c rra rt0 rt1 rt2 ra0 ra2 ra3 ra4 ra5 ra6 ra7 rs2 rt3 rt4 rt5 rt6 valv mm
      Hrem HP0 Hcur HE Hc -> -> -> -> HC HLEN HPPc HSAV ST GSB GOT OLEN OBUF OVAL OPP HBUF HVAL MU WM MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    lx_run_tac (PLAN [0x099d5c] [(0x099d00, DJoin); (0x099d24, DJoin); (0x099d44, DJoin)] 200%N).
    lx_tree.
    all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x099d5c) _ _ ?mm _] => lxc_apply (loopB_walk (Z.to_nat rem) cur rem 0 c)
         | |- _ => idtac
         end.
    all: try lxc_cells_conv.
    all: try (rewrite Z.mul_0_l; lia).
    all: try lx_arith.
  Qed.


  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L12218479608.80 L17807771881.81 L17873211871.82 L20876673400.93 L21556459619.81 L27976822313.124L28252571866.80 L28576966805.2  L32004952509.124L33144429875.80 L39237597384.124L4203851315.125 L49870305618.81 L55259464552.81 L55508994005.2  L56338951363.80 L59314873579.2  L59314873579.3  L59314873579.4  L59314873579.5  L59314988138.1  L59314988138.82 L59501521752.125L63114806148.126L65509483276.124L66379809355.12400000S01C02:05Q06H07l08H08I08h09M09l0:D0:h0;L0;M0<10<20<30<40<50<60<70<O0<n0>R0?1S2sp2PP4VALP3END2bs1k3cur3rem2Hk2HES2sp2PP4VALP3END2bs3PPB4VALB1k3cur3rem2Hk2HE3SPRS2sp2PP4VALP1P2bs3PPB4VALB1k2P03cur3rem2Hk3HP04Hcur3SPRS2AL2CS2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB4BUF03NZ13NZ23SPL3LO03DS13DS23DS32P03cur3rem3rra3rt13rt23ra03ra33rt33rt43rt53rt62mm2Hk4Hrem3HP04Hcur2HES2sp2PP4VALP1P2bs3PPB4VALB1k2P03cur3rem2Hk3HP04Hcur3SPRS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS31k2P03cur3rem2Hk3HP04Hcur2HE3SPRS2sp2PP4VALP2bs1k3rem2Hk3H10FS2sp2PP4VALP2bs1k2P03cur3rem2HkS2sp2PP4VALP2bs3PPB4VALB1k3rem2Hk3SPRS2sp2PP4VALP2bs1k2P03cur3rem2HkS2sp2PP4VALP2bs1k3rem2HkS2sp2PP4VALP3BUF2bs1k3cur3rem2Hk3HBRS2sp2PP4VALP3BUF2bs1k3cur3rem2Hk3HBRFS2sp2PP4VALP2bs1k2P03cur3rem2Hk4HcurFFFFFFS2sp2PP4VALP2bs1k3rem2HkS2sp2PP4VALP2bs1k2P03cur3rem2HkS2sp2PP4VALP1P3END3BUF2lo2bs2B12B32D12D22D33PPB4VALB3SPL3DS13DS23DS31k2P03cur3rem2Hk3HP04Hcur2HE3SPRS2sp2PP4VALP2bs1k2P03cur3rem2Hk".
  Lemma loopA_walk : forall (k : nat) (P0 cur rem : Z)
      (rra rt0 rt1 rt2 ra0 ra2 ra3 ra4 ra5 ra6 ra7 rs2 rt3 rt4 rt5 rt6 valv : word) (mm : mem),
    Z.of_nat k = rem -> 1 <= rem -> P + 2 <= P0 -> P0 <= cur -> cur + rem <= END ->
    rt0 = Z_to_bv 64 (-1 - (cur - P0)) -> ra2 = Z_to_bv 64 (-100) -> ra4 = Z_to_bv 64 (cur - P0 + rem) ->
    ra5 = Z_to_bv 64 (cur - P0) -> ra6 = Z_to_bv 64 P0 -> ra7 = Z_to_bv 64 (-1) ->
    rs2 = Z_to_bv 64 (al_sb AL + Z.shiftr PP 3) ->
    rw_cells asegs mm (bv_unsigned sp + -48) [C8 (Z_to_bv 64 rem)] ->
    rw_cells asegs mm PP [C8 (Z_to_bv 64 cur)] ->
    rw_cells asegs mm (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mm lo (bv_unsigned sp + -48) ->
    ro_cells asegs mm 0x1099f8 [C8 (Z_to_bv 64 (al_sb AL))] ->
    ro_cells asegs mm 0x0f5e50 [C8 (Z_to_bv 64 0x1099f8)] ->
    aobj asegs AL CS mm (bv_unsigned sp + -48) 8 -> aobj asegs AL CS mm BUF (Z.of_nat (length bs)) ->
    aobj asegs AL CS mm VALP 4 -> aobj asegs AL CS mm PP 8 ->
    bytes_at asegs mm BUF bs -> rw_cells asegs mm VALP [C4 valv] ->
    munch W m mm -> wmono asegs m mm -> mem_inv asegs mm ->
    evtA asegs AL CS POST
      (MS (mkR rra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp rt0 rt1 rt2 (Z_to_bv 64 PP) (Z_to_bv 64 (al_sb AL))
               ra0 (Z_to_bv 64 VALP) ra2 ra3 ra4 ra5 ra6 ra7 rs2 (Z_to_bv 64 VALP) s4 s5 s6 s7 s8 s9 s10 s11
               rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 0x099c48) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros P0 cur rem rra rt0 rt1 rt2 ra0 ra2 ra3 ra4 ra5 ra6 ra7 rs2 rt3 rt4 rt5 rt6 valv mm
      Hk Hrem HP0 Hcur HE -> -> -> -> -> -> -> HLEN HPPc HSAV ST GSB GOT OLEN OBUF OVAL OPP HBUF HVAL MU WM MI; [lia|].
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    lx_run_tac (PLAN [0x099c48; 0x099cd0] [(0x099c5c, DJoin)] 200%N).
    lx_tree.
    all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x099cd0) _ _ ?mm _] =>
             (match goal with H : bytes_at _ mm BUF bs |- _ =>
                pose proof (ro_byte_of_bytes asegs mm BUF bs cur H ltac:(lia) ltac:(lia)) as HB end);
             pose proof (byte_range (nth (Z.to_nat (cur - BUF)) bs (Z_to_bv 8 0))) as HBR;
             lxc_apply (exitA_walk P0 cur rem _)
         | |- context [MS _ _ (Z_to_bv 64 0x099c48) _ _ ?mm _] => lxc_apply (IH P0 (cur + 1) (rem - 1))
         | |- _ => idtac
         end.
    all: try lxc_cells_conv.
    all: try lx_arith.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L10629252267.100L20733651295.100L20733651671.96 L28269205667.100L28576966805.2  L29146410867.100L30420241882.95 L31378308326.80 L35765242035.147L36520799513.100L43061431595.78 L55218574504.96 L55218574507.95 L55218575136.100L55508994005.2  L56943858420.67 L59226946966.147L59314988138.1  L59314988138.2  L61474854284.95 L62913317664.147L65432955946.100L65432956833.95 L65432956834.96 L6972793116.60  00000J00Y00h01@01A01f02>02M02a03B03X04204L04f04g05605J05M05N05f06?06[07707S07bS2sp2PP4VALP1P2bs4lxv33H23S2sp2PP4VALP2bsS2sp2PP4VALP2bsS2sp2PP4VALP2bs4lxv43H18FS2sp2PP4VALP2bs3PPB4VALB3SPR4lxv43H18S2sp2PP4VALP2bs4lxv23H18S2sp2PP4VALP2bsS2sp2PP4VALP2bs4lxv3S2sp2PP4VALP3END2bs4lxv34lxv43H22S2sp2PP4VALP2lo2bs3SPLS2sp2PP4VALP1P2bs4lxv33H15S2sp2PP4VALP1P2bs4lxv33H16S2sp2PP4VALP1P2bs4lxv33H21FS2sp2PP4VALP2bsS2sp2PP4VALP2bs4lxv3S1GFS2sp2PP4VALP2bs4lxv23H10S2sp2PP4VALP2bs4lxv34lxv4S2sp2PP4VALP3END2bs4lxv33H22S2sp2PP4VALP3END2bs4lxv33H15S2sp2PP4VALP3END2bs4lxv33H16S2sp2PP4VALP2bs".
  Lemma main_walk : forall (a3 a4 a5 a6 a7 valv : word),
    rw_cells asegs m PP [C8 (Z_to_bv 64 P)] -> rw_cells asegs m VALP [C4 valv] -> bytes_at asegs m BUF bs ->
    mem_inv asegs m -> abase asegs AL m ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m VALP 4 -> aobj asegs AL CS m BUF (Z.of_nat (length bs)) ->
    aobj asegs AL CS m (bv_unsigned sp - 48) 8 ->
    stk asegs m lo (bv_unsigned sp) ->
    evtA asegs AL CS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 VALP) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x099b4c) fc None m (seg_rom asegs)).
  Proof.
    intros a3 a4 a5 a6 a7 valv HPP HVAL HBUF MI AB OPP OVAL OBUF OLEN ST.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    carve_frame 48%nat ST.

    apply (rw_cells_split_CB asegs m (bv_unsigned sp + -48) [] 48 junk [] [8; 40]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    cb8_to_c8 FR (@nil cell).
    lazymatch type of FR with rw_cells _ _ _ (C8 ?w :: _) => rewrite <- (Z_to_bv_bv_unsigned w) in FR end.
    pose proof (sums_getlen_ok AL IMG) as LXSUMS.
    lx_pre.
    lx_run_tac (PLANS [0x099c48; 0x099d0c; 0x099d5c]
                      [(0x099bb4, DJoin); (0x099c1c, DJoin); (0x099c5c, DJoin); (0x099d00, DJoin);
                       (0x099d24, DJoin); (0x099d44, DJoin); (0x099d80, DJoin); (0x099d8c, DJoin)]
                      300%N [SUM_getlenA]).
    lx_tree.
    all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x099c48) _ _ ?mm _] =>
             match goal with
             | HP : rw_cells _ mm PP [C8 (Z_to_bv 64 ?cur)],
               HL : rw_cells _ mm (bv_unsigned sp + -48) [C8 (Z_to_bv 64 ?rem)] |- _ =>
                 lxc_apply (loopA_walk (Z.to_nat rem) cur cur rem)
             end
         | |- _ => idtac
         end.
    all: try lxc_cells_conv.
    all: try lx_arith.
  Qed.
End Walk.

Lemma A_asn1_get_int_spec {L : heap_layout} : forall AL, asan_img_ok AL -> asn1_get_int_stmtA asegs AL A_ASN1_GET_INT.
Proof.
  intros AL IMG. unfold asn1_get_int_stmtA, A_ASN1_GET_INT.
  intros until valv.
  intros HPP HVAL HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI ALWF CSOK AB OPP OVAL OBUF
    OLEN SCS -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HVAL) as VALB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, VALB.
  pose proof (proj1 ST) as LO0.
  eapply main_walk; try eassumption; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
