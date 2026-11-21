(** * Bridge.DEmit.DTop — group D's deliverable: [IBoundary.BrCompressCall].

    The harness's first compress call is one [deflate_m] on S5's fresh state ([zdc_init level])
    with the whole input, [avail_out = compressBound] and [Z_FINISH]; RT's [zr_deflate] is one
    [deflate 4] on [defl_new level 8 15 8 0] with the same input and room.  When RT's call
    returns [Z_STREAM_END] with bytes [enc], S5's returns [Z_STREAM_END] and the same bytes:

    - entry: group M's [dm_entry] relates the two entry states ([dst_rel] with no earlier
      output, [mt_inv]); S5's entry facts are its own ([dinitC_fields], [SV_entry], [dreach]);
    - the call: pair D7 ([BrDeflate.br_deflate_entry]) gives the same return code and the same
      output;
    - S5's consumed count, [total_out] and byte range come from S5's own call contract
      ([DeflateTaintTop.deflate_m_facts]).

    Kernel cost: every unfolding of a harness-level call is stated once over ABSTRACT states
    ([rt_zr_deflate_eq], [zdc_deflate_eq], [deflate_m_eq]) and used by [rewrite]; the fresh
    states are opaque here, so no conversion evaluates a model on them (the ITop pitfall).

    Inputs, all cited directly: a worker's D9 ([DZHeader]) and D13
    ([DStoredIface.br_deflate_stored], closed by [DStored]), a worker's live-symbols
    trailer ([DZTrailLive]), group M's [DMatchIface] and the closed group D pairs. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Deflate DeflateSafe
  RefDeflateRel RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI6 DeflateTaintTop DeflateTaintCall ZTaintC ZApiOkC
  HarnessSmall HarnessCompress ZApiInst ZApiInstC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZRepro.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require IBoundary IProbe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface BrTopDefs BrBlocks BrDeflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module DTT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintTop.
Module ZTC := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.ZTaintC.
Module ZOC := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.ZApiOkC.
Module HC := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.HarnessCompress.
Module HSm := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.HarnessSmall.
Module ZAC := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.ZApiInstC.
Module SI6 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.

(* The fresh states are computed constants; facts about them are S5's own lemmas. *)
Local Strategy opaque [HC.dsC HC.dzC].

(* ------------------------------------------------------------------------- *)
(* 1.  The calls, unfolded once over abstract states                         *)
(* ------------------------------------------------------------------------- *)

Lemma rt_zr_deflate_eq : forall level data t,
  IProbe.rt_entry level data = Some t -> 0 <= zlength data < 2 ^ 60 ->
  ZRepro.zr_deflate level 15 data
  = match RD.deflate 4 t with
    | RD.DfRet code t2 => if Z.eqb code Base.Z_STREAM_END then Some (RD.zs_out (RD.d_strm t2)) else None
    | RD.DfUnmodelled => None
    end.
Proof.
  intros level data t Et Hlen.
  unfold IProbe.rt_entry in Et. cbv zeta in Et. unfold ZRepro.zr_deflate.
  change ZRepro.ZR_STRATEGY with 0.
  destruct (RD.defl_new level 8 15 8 0) as [t0|] eqn:E0; rewrite ?E0 in Et; [|discriminate Et].
  injection Et as <-.
  change (Chunk.zlen data) with (zlength data).
  rewrite <- (dm_compress_bound (zlength data) Hlen).
  reflexivity.
Qed.

Lemma zdc_deflate_eq : forall data ds dz aout,
  ZAC.zdc_deflate data (ZApiInst.mkDZ ds dz) aout 4
  = (let '(s', rc) := SDfl.deflate_core (DS.set_strm ds (DS.cstrm_of_call (mkZCall data aout dz))) 4 in
     (ZApiInst.mkDZ s' (zr_strm (DS.zret_of_cs (DS.ds_strm s') rc)), DS.cs_next_in (DS.ds_strm s'),
      DS.cs_output (DS.ds_strm s'), rc)).
Proof.
  intros data ds dz aout. unfold ZAC.zdc_deflate, SDfl.deflate_m. cbn [ZApiInst.dz_s ZApiInst.dz_z].
  destruct (SDfl.deflate_core (DS.set_strm ds (DS.cstrm_of_call (mkZCall data aout dz))) 4) as [s' rc].
  reflexivity.
Qed.

Lemma deflate_m_eq : forall ds zc,
  SDfl.deflate_m ds zc 4
  = (let '(s', rc) := SDfl.deflate_core (DS.set_strm ds (DS.cstrm_of_call zc)) 4 in
     (s', DS.zret_of_cs (DS.ds_strm s') rc)).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The entry states                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma s5_entry_fields : forall level data, 0 <= level <= 9 ->
  DS.ds_status (IProbe.s5_entry level data) = DS.INIT_STATE /\ DS.ds_pending (IProbe.s5_entry level data) = 0
  /\ DS.ds_lookahead (IProbe.s5_entry level data) = 0
  /\ DS.ds_strstart (IProbe.s5_entry level data) = 0 /\ DS.ds_block_start (IProbe.s5_entry level data) = 0.
Proof.
  intros level data Hl. unfold IProbe.s5_entry. cbv zeta. autorewrite with s5f_strm.
  rewrite (ZTC.dsC_of level Hl).
  pose proof (ZTC.dinitC_fields (fun _ => HSm.g0) level Hl) as F. cbv zeta in F.
  destruct F as (Hst & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _ & _ & _ & Hss & Hbs & Hla & _).
  split; [exact Hst|]. split; [exact Hp|]. split; [exact Hla|]. split; [exact Hss | exact Hbs].
Qed.

(** RT's fresh trees state ([tr_init ts_new]): no symbols, an empty bit buffer. *)
Lemma rt_entry_ts : forall level data t,
  IProbe.rt_entry level data = Some t ->
  RT.ts_symnext (RD.d_ts t) = 0 /\ ZBitsOut.bw_valid (RT.ts_bw (RD.d_ts t)) = 0.
Proof.
  intros level data t E. unfold IProbe.rt_entry in E. cbv zeta in E.
  destruct (RD.defl_new level 8 15 8 0) as [t0|] eqn:E0; rewrite ?E0 in E; [|discriminate E].
  injection E as <-. cbn [RD.setD_strm RD.d_ts].
  unfold RD.defl_new in E0.
  destruct (RC.defl_init2 level 8 15 8 0) as [g|] eqn:E1; rewrite ?E1 in E0; [|discriminate E0].
  injection E0 as <-. cbn [RD.deflate_reset RD.d_ts]. vm_compute. split; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The deliverable                                                       *)
(* ------------------------------------------------------------------------- *)

Theorem br_compress_call : IBoundary.BrCompressCall.
Proof.
  intros level data enc Hl Hb Hlen Hrt.
  assert (Hn0 : 0 <= zlength data) by (unfold zlength; lia).
  destruct (IBoundary.cb_value (zlength data) ltac:(lia)) as [Hcb Hcbb].
  (* RT: the entry state and the call *)
  destruct (dm_entry level data Hl Hb Hlen) as (t & Et & Hrel & _ & Hmt).
  rewrite (rt_zr_deflate_eq level data t Et ltac:(lia)) in Hrt.
  (* S5: the entry state *)
  destruct (ZTC.DCALL_initC (fun _ => HSm.g0) (fun _ => HSm.g0) level Hl) as (_ & _ & _ & Hreach & _).
  rewrite <- (ZTC.dsC_of level Hl) in Hreach.
  destruct (ZOC.dzC_scalars level Hl) as (_ & TO & ZOK).
  assert (Hzc : DSf.dcall_wf (mkZCall data (SDfl.compressBound_m (zlength data)) (HC.dzC level))).
  { unfold DSf.dcall_wf. cbn [zc_strm zc_avail_out zc_input].
    split; [exact ZOK|]. split; [rewrite Hcb; lia|]. split; [lia | exact Hb]. }
  pose proof (SI2.C0OK'_of_call _ Hzc) as HC0.
  assert (HDC : SI1.DC (DS.cstrm_of_call (mkZCall data (SDfl.compressBound_m (zlength data)) (HC.dzC level)))
                       (IProbe.s5_entry level data)).
  { unfold IProbe.s5_entry. cbv zeta.
    split; [apply SI1.DD_set_strm, (SI6.dreach_DD _ Hreach) | apply SI1.SV_entry, Hzc]. }
  destruct (s5_entry_fields level data Hl) as (Hinit & Hp & Hla & Hss & Hbs).
  destruct (rt_entry_ts level data t Et) as [Hsn Hbv].
  rewrite <- (dst_rel_symnext _ _ _ _ Hrel) in Hsn. rewrite <- (dst_rel_bivalid _ _ _ _ Hrel) in Hbv.
  assert (Hroom : DS.cs_total_out (DS.cstrm_of_call (mkZCall data (SDfl.compressBound_m (zlength data)) (HC.dzC level)))
                  + DS.cs_avail_out (DS.cstrm_of_call (mkZCall data (SDfl.compressBound_m (zlength data)) (HC.dzC level)))
                  + 2 ^ 17 < 2 ^ 64)
    by (cbn [DS.cstrm_of_call DS.cs_total_out DS.cs_avail_out zc_strm zc_avail_out]; rewrite TO, Hcb; lia).
  assert (Hao : 0 < DS.cs_avail_out (DS.cstrm_of_call (mkZCall data (SDfl.compressBound_m (zlength data)) (HC.dzC level))))
    by (cbn [DS.cstrm_of_call DS.cs_avail_out zc_avail_out]; rewrite Hcb; lia).
  (* pair D7 *)
  destruct (br_deflate_entry _ (IProbe.s5_entry level data) t [] [] HC0 eq_refl HDC Hroom Hao Hinit Hp Hsn Hla Hbv
              Hss Hbs Hrel Hmt)
    as (code & t' & Edf & Hcode & Hstrm).
  rewrite Edf in Hrt. cbv beta iota in Hrt. revert Hrt.
  destruct (Z.eqb code Base.Z_STREAM_END) eqn:Ecode; intros Hrt; [|discriminate Hrt].
  apply Z.eqb_eq in Ecode. injection Hrt as Henc.
  (* S5: the call's own contract *)
  pose proof (DTT.deflate_m_facts _ _ 4 Hreach Hzc ltac:(lia)) as Hf. cbv zeta in Hf.
  rewrite deflate_m_eq in Hf.
  change (DS.set_strm (HC.dsC level)
            (DS.cstrm_of_call (mkZCall data (SDfl.compressBound_m (zlength data)) (HC.dzC level))))
    with (IProbe.s5_entry level data) in Hf.
  change (ZAC.zdc_init level) with (ZApiInst.mkDZ (HC.dsC level) (HC.dzC level)).
  rewrite zdc_deflate_eq.
  change (DS.set_strm (HC.dsC level)
            (DS.cstrm_of_call (mkZCall data (SDfl.compressBound_m (zlength data)) (HC.dzC level))))
    with (IProbe.s5_entry level data).
  destruct (SDfl.deflate_core (IProbe.s5_entry level data) 4) as [s' rc] eqn:Ec.
  rewrite ?Ec in Hf, Hcode, Hstrm.
  cbn [fst snd] in Hcode, Hstrm, Hf.
  cbn [DS.zret_of_cs DS.zstrm_of_cs zr_output zr_consumed zr_strm zc_input zc_avail_out zc_strm zs_total_out] in Hf.
  destruct Hf as (_ & Hol & Hcons & Htot & Hbytes).
  unfold strm_rel in Hstrm. cbv zeta in Hstrm. destruct Hstrm as (_ & _ & _ & _ & _ & _ & Hout & _).
  cbv beta iota zeta.
  cbn [ZApiInst.dz_z DS.zret_of_cs DS.zstrm_of_cs zr_strm zs_total_out].
  split; [rewrite <- Henc, Hout; reflexivity|].
  split; [rewrite Hcode, Ecode; reflexivity|].
  split; [exact Hcons|].
  split; [rewrite Htot, TO, Z.add_0_l; apply wrap64_id; rewrite Hcb in Hol; lia|].
  exact Hbytes.
Qed.

Print Assumptions br_compress_call.
