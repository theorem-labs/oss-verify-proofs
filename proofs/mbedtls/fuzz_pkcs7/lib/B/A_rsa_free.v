(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface Asn1Aux MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts RepRsa CrtFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_free P_rsa_free.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free A_mpi_free A_free_seq.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_rsa_free () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.P.P_rsa_free.rsa_free_LB"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.RSA_CTX_SIZE"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RSA_FREE_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RSA_FREE_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_st"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "rsa_free_postA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_free.mpi_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_FREE"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "rsa_free_stmtA"; "A_RSA_FREE"].


Definition A_RSA_FREE : Z := 0x0b283c.   (* [comment removed for export] *)
(* [comment removed for export] *)
Notation RSA_FREE_STACK_A := 80 (only parsing).
Definition RSA_FREE_PHI : Z := 13 * AVOL_CALL.
Definition RSA_FREE_FR : Z := 13 * fr_charge 0.

Definition rsa_free_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C : Z) (r : rsa_st) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_free ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1=.O1<.O1;.)Lh',(5.O1=.O1<.O1;.)(6.(7.$0.R13.(8.(9.(:.O17.O16.O15.O14.R12.R11.R10.O13.O12.R?.R>.R=.R<.R;.R:.R9.R8.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R7.R6.R5.R4.)O7.(;.O17.)O6.(<.(2.&40.))R3.(=.O1=.))R2.))(6.(>.O1=.R3.)(6.(?.O1=.R3.O3.(10.&40.O16.))(6.(11.O1.R2.)(6.(12.O1=.O1<.(13.O4.O19.)O18.(10.&40.O16.)(14.O1<.)(15.O1=.O1<.O1;.O1:.)(16.(17.$18.$18.)(19.$18.$18.O5.(1:.O5.$1;.))(1<.(17.$18.$18.)))O2.R3.)(6.(7.$18.(1=.O1=.O1<.O1;.R1.)(1=.O1=.O1<.O1;.O1:.))(6.(7.$18.(15.O1=.O1<.O1;.R1.)(15.O1=.O1<.O1;.O1:.))(6.(7.$18.(1>.O1=.O1<.O1;.R1.)(1>.O1=.O1<.O1;.O1:.))(6.(1?.O1=.O1<.O1;.R1.R2.)(6.Px,$18.P,(20.O1=.O1<.O1;.O1:.R1.)(20.O1=.O1<.O1;.R3.R2.)(6.(21.(22.O1=.O1<.O1;.R1.)(1:.(22.O1=.O1<.O1;.O1:.)$23.))(6.(21.(24.O1=.O1<.O1;.R1.)(1:.(24.O1=.O1<.O1;.O1:.)$25.))(6.(26.O1=.O1<.O1;.R1.(13.O4.O19.)O18.R3.)(27.(17.$18.$18.)(19.$18.$18.O5.$1;.)(13.O4.O19.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rsa_free_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_free ()) "Ph,(5.O4.O3.O2.)PLB,(28.$29.)PLF,(28.$29.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2:.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PC,$18.Pr,$2;.Plo,$18.P,(26.O4.O3.O2.R29.R28.R27.R5.)P,(1?.O4.O3.O2.R2:.R5.)P,(2<.O4.R7.R2:.R5.R4.)P,(?.O4.R8.R4.(10.&40.R28.))P,(21.(14.O3.)R5.)P,(21.R6.(2=.(2=.(10.&40.R2:.)+50.)(2>.O3.)))P,(21.(10.&40.R2;.)(1=.O4.O3.O2.R2?.))P,(7.$18.(2?.(10.&40.R2<.)+10.)=)P,(7.(2.&40.)R2;.(30.&40.(31.O3.)))P,(>.O4.R>.)P,(21.(1:.(22.O4.O3.O2.R33.)$23.)$32.)P,(21.(1:.(24.O4.O3.O2.R34.)$25.)$33.)P,(7.(2.&40.)R29.(30.&40.R?.))(34.O4.(35.O4.O3.O2.R36.R35.R34.R33.R32.R31.R30.R2<.R2;.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R14.R13.R10.R?.R>.R12.R11.)(8.(9.(:.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R14.(30.&40.O1.)R13.(<.(2.&40.))R12.(=.O4.))R11.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Ltac rs_in := cbn [In rsa_free_seq]; repeat (first [left; reflexivity | right]).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x0b28e0]).
Local Ltac zchk_new ::= constr:([0x0b284c; 0x0b2850]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section RF.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis MPIFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.                       (* [comment removed for export] *)
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).              (* [comment removed for export] *)

  Ltac fsA_in ::= rs_in.
  Ltac fsA_addr ::= cbn [md_addr mpd_z]; match goal with AN : md_addr (r_N ?r) = _, AE : md_addr (r_E ?r) = _ |- _ => rewrite ?AN, ?AE | _ => idtac end.

  (* [comment removed for export] *)
  Ltac rsA_free1 spo md X rest :=
    lazymatch goal with
    | HH : HM _ _ _ ?xhc ?xLBc _ ?xmc, PXA : presW _ _ _ ?xh0 ?xLBf _ ?xSP _ [(?xC, _)] ?xm0 _, ST : stk _ _ ?xlo _,
      HBR : blkfacts _ (?xLB ++ _), DISF : mpds_apart ?xFR |- _ =>
        eapply (free_stepA R HIA A_MPI_FREE MPIFREE NEEDR DIMG) with
          (d0 := md) (X0 := X) (A := xC) (sz := 232) (d := 0) (SP := xSP) (h0 := xh0) (m0 := xm0) (LBf := xLBf)
          (lo := xlo) (LBall := xLB) (FR := xFR);
        [ fsA_side spo rest .. | ]
    end;
    lazymatch goal with
    | |- forall _, _ =>
        lazymatch goal with HH : HM _ _ _ _ _ _ _, LIV : Forall (mpdr_at _ _ _) _, CH : Forall _ _, PXA : presW _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          lazymatch goal with HTc : htop _ _ _ _ = _, HSc : hstkhi _ _ _ _ = _, HFc : hflag _ _ _ _ = _, HCSc : (forall x, hcs _ _ _ _ x -> hcs _ _ _ _ x),
                              HV : havol _ _ _ _ <= _, HFR : hfr _ _ _ _ <= _, OBJ : aobj _ _ _ _ _ 232, ST : stk _ _ _ _, MI : mem_inv _ _ |- _ =>
            first [ fsA_post HH HTc HSc HFc HCSc HV HFR LIV CH PXA OBJ ST MI
                  | match goal with |- ?g => idtac "fsA_post FAILED at" g end ]
          end end
    | |- ?g => idtac "rsA_free1: free_stepA left goal" g
    end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "04d0@D13156179990.111D31501237935.110D35881667587.110D35881667587.111K22919320178.110K22919320178.111K37211889074.110K37211889074.111L10740050254.254L11529325383.128L11529325383.146L11529325383.164L11529325383.182L11529325383.200L11529325383.218L11529325383.236L11529325383.254L11529325383.272L11529325383.290L11539923632.108L11774327555.106L13107166054.3  L13696737932.128L13696737932.146L13696737932.164L13696737932.182L13696737932.200L13696737932.218L13696737932.236L13696737932.254L13696737932.272L13696737932.290L13696737932.308L13698952059.108L13989273002.5  L14665872058.218L14678983143.164L15047311160.98 L18487777152.98 L20431817446.327L20431965282.104L20433961190.106L20904914247.128L20904914247.146L20904914247.164L20919182512.108L2150601031.128 L2150601031.146 L2150601031.164 L2150601031.182 L2150601031.200 L2150601031.218 L2160679088.108 L22364848615.254L22725723689.9  L22929803779.2  L23148116410.236L2351528779.128 L2351528779.146 L2351528779.164 L2351528779.182 L2351528779.200 L2351528779.218 L2351528779.236 L2351528779.254 L2351528779.272 L2351528779.290 L2351528779.308 L2364372390.326 L2397629480.6   L24550485946.308L25146143207.128L26892149748.326L27810914126.236L28006793734.106L28633463482.272L30283730608.108L30298326855.128L30298326855.146L30298326855.164L30298326855.182L30298326855.200L30298326855.218L30298326855.236L30879971815.236L30993508591.128L30993508591.146L30993508591.164L30993508591.182L30993508591.200L30993508591.218L30993508591.236L30993508591.254L30993508591.272L30993508591.290L30993508591.308L30997964290.326L30999945496.108L31399144472.326L3172519790.95  L31830027184.108L31840100935.128L31840100935.146L31840100935.164L31840100935.182L31840100935.200L32049487064.105L32049487064.326L32231604335.128L32231604335.146L32231604335.164L32231604335.182L32231604335.200L32231604335.218L32231604335.236L32231604335.254L32231604335.272L32231604335.290L32231604335.308L32241715608.108L32243928706.326L33148225722.290L33306151620.128L33306151620.146L33306151620.164L33306151620.182L33306151620.200L33306151620.218L33306151620.236L33306151620.254L33306151620.272L33306151620.290L33306151620.308L33316750131.108L33318994985.326L33669351805.92 L3523494932.108 L3538062819.128 L3538062819.146 L3538062819.164 L3538062819.182 L3538062819.200 L3538062819.218 L3538062819.236 L3538062819.254 L3538062819.272 L3538062819.290 L3538062819.308 L3538062819.326 L35653441506.7  L36053498343.146L36338336846.200L37222368707.2  L3736507726.308 L3832472834.327 L39662989488.108L39678114119.128L39835269710.218L41598149540.8  L43057599553.104L43360901198.290L46550781791.128L46550781791.146L46550781791.164L46550781791.182L46550781791.200L46550781791.218L46550781791.236L46550781791.254L46550781791.272L46550781791.290L46550781791.308L46748113268.105L48132467214.7  L48378946382.182L49527994922.108L49543115741.128L49543115741.146L49543115741.164L49543115741.182L49543115741.200L49543115741.218L49543115741.236L49543115741.254L49543115741.272L49543115741.290L49543115741.308L50590611376.108L50592333383.128L50592333383.146L50592333383.164L50592333383.182L50592333383.200L50592333383.218L50592333383.236L50592333383.254L50592333383.272L50592333383.290L50592333383.308L51518038503.326L51887800654.164L52112650108.108L52524925320.5  L54261977575.200L55385253710.146L55978761415.326L56552377779.106L56552377779.326L57569565159.308L58421476528.108L58771596730.128L59236546647.326L59308628179.3  L59969837488.108L59972112455.128L59972112455.146L59972112455.164L59972112455.182L60098763854.3  L60208049082.164L60334590439.182L60410904739.326L610388551.128  L610388551.146  L610388551.164  L610388551.182  L610388551.200  L610388551.218  L610388551.236  L610388551.254  L612828080.108  L61494492999.128L61494492999.146L61500929712.108L61966193127.290L62018535662.1  L62760393191.218L63117452621.108L63913911737.108L6445894742.98  L65756476346.254L66099488952.3  L66299915094.108L67177718202.146L67431951009.128L67431951009.146L67431951009.164L67431951009.182L67431951009.200L67431951009.218L67431951009.236L67431951009.254L67431951009.272L67431951009.290L67431951009.308L67438584662.108L67439886926.272L68037757415.272L68353477445.128L68353477445.146L68353477445.164L68353477445.182L68353477445.200L68353477445.218L68353477445.236L68353477445.254L68353477445.272L68353477445.290L68353477445.308L68363584178.108L68365796776.326L7247448910.128 L7697245370.200 L90242490.182   L9990171719.128 L9990171719.146 L9990171719.164 L9990171719.182 L9990171719.200 L9990171719.218 L9990171719.236 L9990171719.254 L9990171719.272 L9992086960.108 Q13296972522.108Q14525642139.110Q15641306337.327Q15643324129.106Q20685106778.111Q22712450012.110Q22712450012.111Q25513505925.109Q25513505925.110Q36801578553.110Q3830427394.107 Q3832472834.327 Q45914037331.107Q49698585326.108Q49698585326.109Q51233783137.327Q51235796833.107Q522895370.110  Q522895370.111  Q58146298210.109Q67528989526.110Q67528989526.111Q9841186690.327 Q9843367298.106 00000b01T02:02`03S04F04j05N05T05Z05`05f05l06206806>06D06J06P06V06\06e07807K07^08108D08W08j09=09P09c0:60:I0:Y0:_0:e0:k0;10;70;=0;C0;I0;O0;U0;[0;a0;g0;m0<30<90<?0<E0<K0<c0<d0<j0<k0<l0<m0<n0<o0=00=10=20=30=40=50=G0=[0=a0=g0=m0>30>?0>E0>K0>Q0>W0>]0>c0>i0>o0?50?;0?c0@K0@d0A=0AV0Ao0BH0C00CX0D@0DY0D_0EG0EM0ES0EY0E_0Ee0Ek0F10F70F=0FC0FD0FE0FF0FG0FH0FI0FJ0FK0FL0FM0FN0FO0Fb0Fh0G70GF0GU0Gd0H30HB0HQ0H`0Ho0I>0IM0I\0Ik0J60JO0Jh0KA0KZ0L30LL0Le0M>0MW0N00NI0Nb0O;0OU0O[0Oa0Ob0Oh0PD0PJ0PP0PV0Pm0QI0QO0Qa0R30RE0RW0Ri0S;0SM0S_0T10TC0TU0T[0U60U<0UB0UH0UN0UT0UZ0U`0Uf0Ul0V20V80V>0VD0VJ0VP0VV0V\0Vb0Vh0Vn0W40W:0W@0WF0WL0WR0WX0Wj0X;0XA0XG0XM0XS0XY0X_0Xe0Xk0Y10Y:0Y@0YF0YL0YR0YX0Yb0Yh0Yn0Z40Z:0Z@0ZF0ZL0ZR0ZX0Z^0Zd0Zj0[00[60[<0[B0[E0[K0[Q0[W0[]0[c0[l0[m0\30\P0\m0]J0]g0^D0^a0_>0_[0`80`U0a20aO0aU0a[0aa0ag0am0b30b90b?0bE0bK0bQ0bW0b]0bc0bi0bo0c50c;0cA0cG0cM0cS0cY0c_0ce0ck0d10d70d>0dk0e20e90ef0f<0fR0fk0gD0gi0h<0hO0hV0hg0i80i?0iF0iG0iH0im0jR0k70kJ0k]S1R5NEEDR2sp2s01C2lo2C03LOS3SLO3SPR2HB5Ha_st5Hl_stS1R5NEEDR2ra2sp1C2lo2C03LOS3SLO3SPR2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp1C5SPTOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s01C5SPTOP2HB5Ha_st5Hl_stS1R5NEEDR2ra2sp1C2lo3LOS3SLO3ALO3C4_2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01C2lo3LOS3SLO3ALO3C4_2HB5Ha_st5Hl_stS1R2ra2sp1C3C4_5ACLsp2HB5Ha_st5Hl_stS1R2sp2s01C3C4_5ACLsp2HB5Ha_st5Hl_stS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS1R3HIA1hS1R3HIA1h2sp1C4BUDFS1R3HIA1h2sp1C4BUDFS1R3HIA1h2sp1C4BUDFS1R3HIA1h2sp1C4BUDFS1R3HIA1h2sp1C4BUDFS1R3HIA1h2sp1C4BUDFS1R3HIA1h2sp1C4BUDFS1R3HIA1h2sp1C4BUDFS1R3HIA1h2sp1C4BUDFS1R3HIA1h2sp1C4BUDFS1R3HIA1h2sp1C4BUDFS1R3HIA1h2sp1C4BUDFS1R3HIA1h3h122HVS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS1R2sp2lo3LOS3ALO1a1n2HnFS2sp1CFFFFFFFFFFFS1R3HIA1h2sp1C3BUDS1R1C2lo3LOS3ALO3C4_S2sp1CS2sp1CS2sp1CS2sp1CS2sp1C2C02CBS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1C1R5NEEDR2lo2C03LOS3SLO3ALO3SPR3C4_S2sp1C1R5NEEDR2lo2C03LOS3SLO3ALO3SPR3C4_S2sp1C1R2C03SPR3C4_5ACLspS2sp1C1R2C03SPR3C4_5ACLspS2sp1C1R2C03SPR3C4_5ACLspS2sp1C1R2C03SPR3C4_5ACLspS2sp1C1R2C03SPR3C4_5ACLspS2sp1C1R5NEEDR2lo2C03LOS3SLO3ALO3SPR3C4_S2sp1C1R5NEEDR2lo2C03LOS3SLO3ALO3SPR3C4_S2sp1C1R5NEEDR2lo2C03LOS3SLO3ALO3SPR3C4_S2sp1C1R2C03SPR3C4_5ACLspS2sp1CS2sp1C1R5NEEDR2lo2C03LOS3SLO3ALO3SPR3C4_S2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CFFFFFFFFFFFFS1R3HIA1h2sp1C4BUDFS2sp1CS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS1R2sp1C2lo3SLOS2sp1C1a2HaS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R2sp1C2C03ACV3SPR5ACLspS1R3HIA1h2sp2lo5SPTOP4HTOPS2sp1CS2sp1CFS2sp1CS1R5NEEDR2sp1C2lo2C03SLO3SPRS2sp1CS2sp1CS2sp1CS1R2sp1C2lo3LOS3ALO3C4_S1R5NEEDR2sp1C2lo2C03SLO3SPRS2sp1CS1R3HIA1h2sp1C3BUDS1R3HIA1h2sp1C3BUDS1R3HIA1h2sp1C3BUDS1R3HIA1h2sp1C3BUDS1R3HIA1h2sp1C3BUDS1R3HIA1h2sp1C3BUDS1R3HIA1h2sp1C3BUDS1R3HIA1h2sp1C3BUDS1R3HIA1h2sp1C3BUDS1R3HIA1h2sp1C3BUDS1R3HIA1h2sp1C3BUDS2sp1CS1R5NEEDR2sp2lo3LOS3SLO3ALOS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS1R3HIA1h2sp1C3BUDS1R3HIA1h3h123HFRS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS1C2C02K0S2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS1R2lo3LOSS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS1RS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS1R3HIA1hFS2sp1CS1R2sp1C2C03SPA3ACV3SPR5ACLspS1R2sp1C2C03SPA3ACV3SPR5ACLspS1R2sp1C2C03SPA3ACV3SPR5ACLspS1R2sp1C2C03SPA3ACV3SPR5ACLspS1R2sp1C2C03SPA3ACV3SPR5ACLspS1R2sp1C2C03SPA3ACV3SPR5ACLspS1R2sp1C2C03SPA3ACV3SPR5ACLspS1R2sp1C2C03SPA3ACV3SPR5ACLspS1R2sp1C2C03SPA3ACV3SPR5ACLspS1R2sp1C2C03SPA3ACV3SPR5ACLspS1R2sp1C2C03SPA3ACV3SPR5ACLspS1R2sp1C2C03SPA3ACV3SPR5ACLspS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp1CS2sp2HBS1R5NEEDR2ra2sp2lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS2sp2loS2sp2loS1R5NEEDR2sp2s02lo3LOS3SLO3ALO2HB5Ha_st5Hl_stS2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_stS2ra2sp2lo2HB5Ha_st5Hl_stS2sp2s02lo2HB5Ha_st5Hl_stS1R5NEEDR2sp2s02lo3SLO2HB5Ha_st5Hl_stS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2HBS2sp3SPR2HB5Ha_stS2sp3SPR2HB5Ha_stS2sp2loS2sp2loFFS1R5NEEDR2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R5NEEDR2ra2sp2lo3SLO2HB5Ha_st5Hl_stS1R5NEEDR2sp2s02lo3SLO2HB5Ha_st5Hl_stS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLO". (* [comment removed for export] *)
  #[using="MPIFREE NEEDR DIMG HMND"] Lemma A_rsa_free_walk : rsa_free_stmtA asegs R HIA A_RSA_FREE.
  Proof.
    unfold rsa_free_stmtA, A_RSA_FREE. intros until lo.
    intros HH HK0 RA_ ST LOS SLO SPTOP SPA TP MI BUD BUDF ->.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (hcs_stack asegs R HIA h) as SCS0.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SPTOP HTOP; lia]). clear SCS0.
    pose proof (HMND _ _ _ _ HH) as NDL. pose proof DIMG as [DI1 DI2].
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HBR HAP]. change (blkfacts L (LB ++ LF)) in HBR.
    ddestruct RA_ as (HD & HT & AN & AE & [OWNN _] & [OWNE _] & LEN & ALL & CAL & C0 & CB & CIN & PN & PE & PNE).
    unfold RSA_CTX_SIZE in CB, CIN. unfold rsa_head_cells in HD. unfold rsa_tail_cells in HT.
    destruct (blkfacts_in L _ _ _ HBR ltac:(apply in_app_iff; left; exact CIN)) as (_ & _ & C4_ & C5_).
    set (LBf := lb_free_mpds (rsa_free_seq C r) LB).
    assert (SUBF : forall b, In b LBf -> In b LB) by (intros b Hb; eapply lb_free_mpds_sub; exact Hb).
    assert (CINf : In (C, 232) LBf).
    { subst LBf. rewrite rsa_free_LB_eq. apply rsa_free_LB_keep; [exact CIN| exact PN| exact PE]. }
    assert (CW : client_wrange L (LBf ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) C 232).
    { intros a Ha. right; right. exists (C, 232). split; [apply in_app_iff; left; exact CINf| cbn; lia]. }
    assert (ALLM : forall d, In d (rsa_free_seq C r) -> mpdr_at asegs m LB d).
    { intros d Hd. apply (proj1 (Forall_forall _ _) ALL). apply (proj1 (rsa_free_seq_mpds C r d)). exact Hd. }
    assert (NI : forall d, In d (rsa_free_seq C r) -> md_own d = LHeap -> ~ In (md_p d, 4 * md_n d) LBf).
    { intros d Hd O. subst LBf. apply lb_free_mpds_notin; assumption. }
    assert (DISF : mpds_apart (rsa_free_seq C r)).
    { intros d1 d2 H1 H2 NE O1 O2.
      destruct (rsa_free_seq_heap _ _ _ H1 O1) as [-> | ->]; destruct (rsa_free_seq_heap _ _ _ H2 O2) as [-> | ->];
        [exfalso; apply NE; reflexivity| exact (PNE O1 O2)| intros E; exact (PNE O2 O1 (eq_sym E))| exfalso; apply NE; reflexivity]. }
    assert (ACLsp : alloc_ceiling <= bv_unsigned sp) by (clear - ALO LOS SLO NEEDR; lia).
    pose proof (free_facts_introA asegs R HIA h LB LF LBf m (bv_unsigned sp) _ C 232 (rsa_free_seq C r) HH NDL ALLM CW SUBF NI ACLsp ltac:(lia) DI1 DI2) as FF1.
    assert (SX : C + 232 <= lo \/ bv_unsigned sp <= C) by (left; clear - C4_ ALO LOS; lia).
    pose proof (hm_aobj_block asegs R HIA h LB LF m C 232 HH CIN) as OBJ.
    pose proof (uw_obj_block asegs R HIA h LB LF m C 232 C 232 0 HH ltac:(apply in_app_iff; left; exact CIN) ltac:(lia) ltac:(lia) ltac:(lia)) as UWO.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK0 (mo_frame_refl mo))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    pose proof (presW_sub_blocks asegs R HIA h LB LBf LF (bv_unsigned sp) (arl_stklo R) [(C, C + 232)] m m
                  (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [(C, C + 232)] HH ltac:(clear; lia)) SUBF) as PXA.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    pose proof (conj ALL I) as ALLbox. pose proof (conj MI I) as MIbox. clear ALL ALLM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - C0 CB; lia); clear - K0 C0; lia|]. clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    destruct ALLbox as [ALL _]. destruct MIbox as [MIm _].
    assert (LIV : Forall (mpdr_at asegs m1 LB) (rsa_free_seq C r)).
    { eapply (lives_munchA asegs L m m1 LB (LB ++ LF)); [| exact MU0| exact WM0| exact MIm| assumption| exact HBR| intros b Hb; apply in_app_iff; left; exact Hb| | intros a n Ha Hn; cbn; clear - Ha Hn ALO LOS; lia].
      - apply Forall_forall. intros d Hd. apply (proj1 (Forall_forall _ _) ALL). apply (proj1 (rsa_free_seq_mpds C r d)). exact Hd.
      - unfold rsa_free_seq. repeat apply Forall_cons; try apply Forall_nil; cbn [md_addr mpd_z]; rewrite ?AN, ?AE; cbn; clear - C4_ ALO LOS SX; lia. }
    clear ALL MU0 WM0 MIm.
    lazymatch goal with HDx : rw_cells _ m1 C _, HTx : rw_cells _ m1 (C + 224) _, F : rw_cells _ m1 (bv_unsigned sp + -16) ?cs |- _ =>
      assert (CH : Forall (fun ac => rw_cells asegs m1 (fst ac) (snd ac))
                     [(C, [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (r_len r))]); (C + 224, [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]); (bv_unsigned sp - 16, cs)])
        by (repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [exact HDx| exact HTx| replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact F]);
      clear HDx HTx F end.
    pose proof (eq_refl (htop asegs R HIA h)) as HTc. pose proof (eq_refl (hstkhi asegs R HIA h)) as HSc. pose proof (eq_refl (hflag asegs R HIA h)) as HFc.
    assert (HCSc : forall x, hcs asegs R HIA h x -> hcs asegs R HIA h x) by (intros x Hx; exact Hx).
    assert (HV : havol asegs R HIA h <= havol asegs R HIA h + 0 * AVOL_CALL) by (clear; lia).
    assert (HFR : hfr asegs R HIA h <= hfr asegs R HIA h + 0 * fr_charge 0) by (clear; lia).
    unfold RSA_FREE_PHI in BUD. unfold RSA_FREE_FR in BUDF.
    lazymatch goal with STx : stk _ m1 lo _, MIx : mem_inv _ m1 |- _ => rename STx into ST; rename MIx into MI end.
    (* [comment removed for export] *)
    zstep.
    rsA_free1 (bv_unsigned sp + -16) (mpd_z (C + 192)) (C + 192)
      [mpd_z (C + 208); mpd_z (C + 144); mpd_z (C + 48); mpd_z (C + 80); mpd_z (C + 64); r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)].
    zstep. zstep. rsA_free1 (bv_unsigned sp + -16) (mpd_z (C + 208)) (C + 208)
      [mpd_z (C + 144); mpd_z (C + 48); mpd_z (C + 80); mpd_z (C + 64); r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)].
    zstep. zstep. rsA_free1 (bv_unsigned sp + -16) (mpd_z (C + 144)) (C + 144)
      [mpd_z (C + 48); mpd_z (C + 80); mpd_z (C + 64); r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)].
    zstep. zstep. rsA_free1 (bv_unsigned sp + -16) (mpd_z (C + 48)) (C + 48)
      [mpd_z (C + 80); mpd_z (C + 64); r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)].
    zstep. zstep. rsA_free1 (bv_unsigned sp + -16) (mpd_z (C + 80)) (C + 80)
      [mpd_z (C + 64); r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)].
    zstep. zstep. rsA_free1 (bv_unsigned sp + -16) (mpd_z (C + 64)) (C + 64)
      [r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)].
    zstep. zstep. rewrite <- AE. rsA_free1 (bv_unsigned sp + -16) (r_E r) (md_addr (r_E r))
      [r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)].
    zstep. zstep. rewrite <- AN. rsA_free1 (bv_unsigned sp + -16) (r_N r) (md_addr (r_N r))
      [mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)].
    zstep. zstep. rsA_free1 (bv_unsigned sp + -16) (mpd_z (C + 176)) (C + 176)
      [mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)].
    zstep. zstep. rsA_free1 (bv_unsigned sp + -16) (mpd_z (C + 160)) (C + 160)
      [mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)].
    zstep. zstep. rsA_free1 (bv_unsigned sp + -16) (mpd_z (C + 128)) (C + 128)
      [mpd_z (C + 112); mpd_z (C + 96)].
    zstep. zstep. rsA_free1 (bv_unsigned sp + -16) (mpd_z (C + 112)) (C + 112)
      [mpd_z (C + 96)].
    (* [comment removed for export] *)
    fa_get CH 14%nat CFR. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) in CFR by lia.
    zstep. zstep. zstep. zstep. release_frame CFR ST (bv_unsigned sp).
    try (replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    lazymatch type of CH with Forall ?P ?CS =>
      let pre := eval cbn [removelast] in (removelast CS) in
      assert (CH' : Forall P pre) by (apply (proj1 (proj1 (Forall_app P pre [(bv_unsigned sp - 16, [C8 s0; C8 ra])]) CH)));
      clear CH; rename CH' into CH end.
    zstep. rsA_free1 (bv_unsigned sp) (mpd_z (C + 96)) (C + 96) ([] : list mpd).
    (* [comment removed for export] *)
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold rsa_free_postA. deexists 15.
    lazymatch goal with HH : HM _ _ _ ?h2 _ _ ?m2 |- _ => exists m2, mo9, h2 end.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF9|].
    subst LBf. rewrite rsa_free_LB_eq in PXA, CINf.
    split; [exact (presW_presA asegs R HIA h _ LF _ _ _ _ _ PXA)|].
    split; [exact HTc|]. split; [exact HSc|]. split; [exact HFc|]. split; [exact HK9|]. split; [exact HCSc|].
    split; [unfold RSA_FREE_PHI; clear - HV; lia|]. split; [unfold RSA_FREE_FR; clear - HFR; lia|].
    split; [| exact CINf].
    lazymatch type of HH with HM _ _ _ _ ?l _ _ => change l with (lb_free_mpds (rsa_free_seq C r) LB) in HH end.
    rewrite rsa_free_LB_eq in HH. exact HH.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RF.

Lemma A_rsa_free_spec : ltac2:(CDefT.buildp (gd_tbl_A_rsa_free ()) "PR,$36.PHIA,(37.$38.R1.)P,(39.(3:.R2.))P,(3;.$38.R3.R2.$3<.)P,(21.=(2>.R4.))P,(6.(21.(3=.(3>.R5.))(3?.(3>.R5.)))(21.(40.(3>.R5.))(41.(3>.R5.))))P,Ph,(5.$38.R6.R5.)PLB,(28.$29.)PLF,(28.$29.)Pm,P,(2.&40.)(3.(2.&8.))P,(26.$38.R:.R9.R4.R3.R2.R1.)(42.$18.(43.(17.$18.$18.)$18.(44.$18.$18.)R4.))(45.$38.R7.R6.$46.)")
(* [comment removed for export] *).
Proof. intros. eapply A_rsa_free_walk; eauto. Qed.
