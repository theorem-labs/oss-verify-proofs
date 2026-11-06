(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Export ExecF ITreeA NodesA StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_SysStepF () := "I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA:implF_evtFC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA8SysStepF?implF_post_evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01".
Import ListNotations.
Import Exc.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation implA segs RNG t Q ms := (@implF node segs (at_nodeA segs) fstepA _ RNG t Q ms).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma implF_from_evtF : forall {node : Type} segs (atn : node -> footprint -> machine_state -> Prop)
    (fst : node -> resp -> footprint -> footprint -> Prop) {R} RNG (t : itree node R) Q ms,
  evtF segs RNG (fun ms' => implF segs atn fst RNG t Q ms') ms -> implF segs atn fst RNG t Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStepF ()) [] "h03ms'h11Hh22H'h31Qh41Rh53RNGh63atnh73fsth82msh94nodeh:4segsh;1tp;1p;2p;9p;4p;<p200R0g0000R1p4p710p8P0g000fR2p4p710p8p203R3P2p4p7511110p8P3g001\R4p4p7511110p8g002Wj14TP1j23TP2l90Tg0037j41TP4l<2Tg003k#4f1R4g004jR2g005cR1p-0R5[[R6[f2R7g006jP5\2\2[[f5R5/34P6\7f7R6f3R8f9R9f8R:P6f6R;P5f4R<P8P7f0R=M90X01P=C1P9P:P6P;P5P<P8P7f:R7P9P:P6P;P5P<P8P=M90X01P4P=f;P7P9P:P6P;P5P<P=M90X01P=O1P=W2X01M<2W1X81W3W;X52X43W7W6W:X90o"). Qed.

Ltac iprefix := apply implF_from_evtF.
Ltac ihere := apply evtF_done.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac at_nodeA_red :=
  cbn [at_nodeA ncov at_node]; unfold areg, max_write, max_read, TASK_SIZE, cstr_len, path_max;
  cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS];
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let R' := eval hnf in R in
      change (reg_get R r) with (match tget p R' with Some v => v | None => w0 end);
      cbv beta iota delta [tget]
  end.

Ltac at_nodeA_solve :=
  at_nodeA_red; split_spine;
  first [ reflexivity | lia | assumption | exact I
        | solve_rng
        | lazymatch goal with |- _ = _ \/ _ = _ => first [left; reflexivity | right; reflexivity] end
        | symmetry; apply Z_to_bv_bv_unsigned
        | lazymatch goal with
          | |- wr_at ?segs ?m ?A ?n =>
              match goal with H : rw_cells segs m A ?cs |- _ =>
                apply (rw_cells_wr_at segs m A cs n H); cbn [cells_size csize]; lia end
          | |- bytes_at ?segs ?m ?A ?bs =>
              match goal with
              | H : rw_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (rw_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              | H : ro_cells segs m A ?cs |- _ =>
                apply (bytes_at_ext segs m A _ bs (ro_cells_bytes_at segs m A cs H));
                cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
              end
          | |- _ /\ _ => split; at_nodeA_solve
          end
        | idtac ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fstep_transport HF :=
  lazymatch type of HF with
  | fstepA ?n ?rsp ?RNG ?RNG' =>
      first
        [ (* [comment removed for export] *)
          lazymatch eval hnf in (fstepA n rsp RNG RNG') with
          | RNG' = RNG => idtac
          end;
          let E := fresh in assert (E : RNG' = RNG) by exact HF; subst RNG'; clear HF
        | lazymatch n with
          | NMunmap ?a ?l =>
              repeat match goal with
              | H : rng RNG ?lo ?len |- _ =>
                  first [ apply (fstepA_munmap_rng a l rsp RNG RNG' lo len HF) in H; [| reglia]
                        | idtac "note: dropping footprint hypothesis (overlaps the unmapped range):" H; clear H ]
              end
          | _ =>
              repeat match goal with
              | H : rng RNG ?lo ?len |- _ =>
                  apply (fstepA_rng n rsp RNG RNG' lo len I HF) in H
              end
          end ]
  end.

(* [comment removed for export] *)
Tactic Notation "fstep_intro" ident(rsp) ident(RNG') ident(a) ident(HF) ident(Hdec) :=
  intros rsp RNG' a HF Hdec; fstep_transport HF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac sys_mem_write :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?ro) =>
    change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
    lazymatch goal with
    | H : rw_cells segs m B [CB ?n ?junk] |- _ =>
        let HB := fresh "HB" in
        pose proof (rw_cells_bound segs m B _ H) as HB; cbn [cells_size csize Nat.add] in HB;
        (try lazymatch goal with
         | HI : mem_inv segs m |- _ =>
             let HI' := fresh "MI" in
             pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
         end);
        let H' := fresh "DST" in
        pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
        clear H;
        transport_chunks segs m B bs;
        footprint_after_store segs m B bs;
        let m' := fresh "m" in
        remember (write_to_mem m (wa B) bs) as m' eqn:Heqm;
        clear Heqm; clear HB; try clear m; rename H' into H
    | _ => fail "sys_mem_write: no hypothesis rw_cells" segs m B "[CB _ _]"
    end
  end.

Ltac sys_mem_zeros :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (apply_zeros ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_zeros m [(A, Z_to_bv 64 n)]) with (apply_zeros m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hza" in let Hn := fresh "Hzn" in let Han := fresh "Hzan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    transport_zeros segs m a n Ha Hn Han;
    let Z' := fresh "ZNEW" in
    pose proof (rw_cells_zeros_new segs m a n Ha Hn Han) as Z';
    let m' := fresh "m" in
    remember (apply_zeros m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
    clear Heqm Ha Hn Han; try clear m
  end.

Ltac sys_mem_unmaps :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_unmaps m [(A, Z_to_bv 64 n)]) with (apply_unmaps m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hua" in let Hn := fresh "Hun" in let Han := fresh "Huan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    transport_unmaps segs m a n Ha Hn Han;
    let m' := fresh "m" in
    remember (apply_unmaps m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
    clear Heqm Ha Hn Han; try clear m
  end.

Ltac sys_nret :=
  cbv beta delta [efferr_ci eff0_ci efferr eff0];
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_none
        | rewrite apply_mem_delivered; sys_mem_write
        | rewrite apply_mem_write; sys_mem_write
        | rewrite apply_mem_zeros; sys_mem_zeros
        | rewrite apply_mem_unmaps; sys_mem_unmaps
        | idtac ].

Ltac sys_nret_raw :=
  cbv beta delta [efferr_ci eff0_ci efferr eff0];
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps | rewrite apply_mem_none | idtac ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fp_use FP :=
  lazymatch type of FP with
  | ?A /\ ?B =>
      let F1 := fresh "FP" in let F2 := fresh "FP" in
      destruct FP as [F1 F2]; fp_use F1; fp_use F2
  | ?R' = ?R => first [ subst R' | subst R | idtac ]
  | fp_le ?R ?R' =>
      repeat match goal with
      | H : rng R ?lo ?len |- _ => apply (rng_fp_le R R' lo len FP) in H
      end
  | fstepA _ _ _ _ => fstep_transport FP
  | rng _ _ _ => idtac
  | _ => idtac
  end.

(* [comment removed for export] *)
Lemma implF_post_evtF : forall {node : Type} segs (atn : node -> footprint -> machine_state -> Prop)
    (fst : node -> resp -> footprint -> footprint -> Prop) {R} (t : itree node R) RNG Q Q' ms,
  implF segs atn fst RNG t Q' ms ->
  (forall r RNG' ms', Q' r RNG' ms' -> evtF segs RNG' (Q r RNG') ms') ->
  implF segs atn fst RNG t Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStepF ()) [] "h04RNG'h13rsph21Qh32Q'h43RNGh52msh63ms1h73ms'h81rh91Hh:2H0h;2HQh<1th=1xh>2HFh?3Hath@2HkhA2IHhB1RhC3atnhD3fsthE1khF1nhG4nodehH4segshI2x0p;1p;2p;9p;4p;3p;7p;6p200R0g0000R1p4p710p8P0g000fR2p4p710p8p203R3g007]R4p4p7210p8P3P2p4p7511110p8g002Wj1;TP1j23TP2l90Tg0037j45Tg008Uj36Tg009Kj7:Tg00:Cj44Tg00;9j21Tg00;lR2j22Tg00<Gj48Tg00<bj77TP4j69Tg003k#;f1R4g004jR1g005cR5p-0R6[R7[R8[f2R9g006jR:P6\1\1[[f4R6f0R;'3f5R<P413<4f3R=P7^I1R7]=R>P8\6R?f:R@f9RAf8RBf7RCf6RDP=P6P4P;M90P<P9P4P;O3REf>RFP9PCP=P9O2RGP4C5[^75^01^8CRHf<RIf;RJP@PAPBP<PDP6P9M90[[^55]3]2^41W<P@PAPBPCPDP=A6@D6P4P;M90PJP<P=PDP<O2P6PDP<O2P9P4P6PCPDP;O3P9PBPCP4P;O4W:X75F:PIPJP@PAPBP<A6IBDP6P9M90eX;HW9X55X3?X2>X41X8413C=\:P7^=<R7P8\DR8PIPJP@PAPBP=P<P6O1P4P;M90f@R>P9PGP4C5\E^75^01^8AREPFf=RGPIPJP@P<PCPDO1P6P9M90[[^55]3]2^41\:PIPJP@PAPBP=PIPBPDP<C4P4P;M90PGP<PGPAPDP;O3RDPFPJP4PBP;O4R?fBRHfARKP>f?RLPFP4PJP9O1RMPC11=9RNM90[^01^1:'2X65PHPKP>PLPFP4PMPBPNM90\?^01^1:,2DX65P9P4PFP@PCP;O3PLPIP4PAP;O4RDfCR?PHPKP>PLP4PIP9O1RMPBPNM90[^01^1:'2X65P;O1P2PFP@PCP4O3P?PHPKP>PLP4PMPB1169M90\D^01^1:PLPJPBP9O3P>PGP4P@P;O4fDRDP?PHPKP>P4PGP9O1P@11<9M90[^01^1:'2P;P>PIPAP=O3PHPLP4PIP;O4fFRKfERMPDP?PHP4PLP9O1PJ11C9M90[^01^1:PHPFPJP<O3P?P>P4PGP;O4RHfGPKPMPDP?P4P>P9O1PG11B9R>M90[^01^1:P4PLP9P4PGPIP>P=P9P4P;O3PAO7X>HX01X1:C8W@W?P4P;O2n2001000000120000000W:X65F7PFPGPIPJP@P<PFP@PBPCC4P6P9M90eX;EW9X55X38X27X41WAWEXF<P;E9W<XB3WDWCWHXG0o"). Qed.

Lemma implF_epost_evtF : forall {node : Type} segs (atn : node -> footprint -> machine_state -> Prop)
    (fst : node -> resp -> footprint -> footprint -> Prop) {A} (t : itree node (exc A)) RNG Q Q' ms,
  implF segs atn fst RNG t (epostF Q') ms ->
  (forall a RNG' ms', Q' a RNG' ms' -> evtF segs RNG' (Q a RNG') ms') ->
  implF segs atn fst RNG t (epostF Q) ms.
Proof.
ltac2:(KReplay.run1 (kr_t_SysStepF ()) [] "p'0h04RNG'h13ms'h22Hph31ai001ah41Ah51Hh62HQh71Qh82Q'h93RNGh:3atnh;3fsth<2msh=4nodeh>1rh?4segsh@1thA1xhB2x0i011ep;1p;2p;9p;4p;5p;<p200R0g00=[R1p4p710p8P0g0000R2p4p710p8P0g000fR3p4p710p8p203R4P1p4p7511110p8P4P3p4p7511110p8P4g00>]R5p4p710p8g002Wj1;Tg00?TR6j14TP2j29TP5j23j51j42TP3l9:Tg0037j40Tg00@Lj16Tg00ADj58Tg00B=j25TP1l<7Tg003k#;f1R1g004jR3g005cR5p-0R2[R7[R8[f2R9g006jP2\3\3[[f4R2f0R:#4'9P7^B3^A9f3R7P8[f9R8f8R;f7R<f6R=f5R>#4P7P213>1P:M9:P>P9P1P:O3f=R?P9P<P7P9O2P1C0[^15^03^3=f;R@f:RAP8P;%4<RBP=P>13<213<7P9P1P6P;P@P<P9P1P:D1f?P9f<R<P8P7P9C2P1C0[^15^03P:PAP=%6AP1P:D1f>R6P9P@P;%6@P9C2R@P1g00C5D8P6P9P@P1C0eW2X15X03P<P;15<9P1P:D1P=P7P9P1P:O4f@P9P?PA15?7P9C2P1C0eW2X15X03X38P:O1n10110100020010100X>BM<7W6W5X<5W8W7X93W@X44W;W:W?X=0o"). Qed.

(* [comment removed for export] *)
Tactic Notation "icall" uconstr(SPEC) :=
  (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
  first [ eapply SPEC
        | eapply implF_epost_mono; [ eapply SPEC | ] ];
  try (lazymatch goal with |- rng _ _ _ => solve_rng end).

(* [comment removed for export] *)
Tactic Notation "icallk" uconstr(SPEC) :=
  (lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
  eapply implF_epost_evtF; [ eapply SPEC | ];
  try (lazymatch goal with |- rng _ _ _ => solve_rng end).

(* [comment removed for export] *)
Ltac ipost segs :=
  let a := fresh "ans" in let RNG' := fresh "RNG" in let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros a RNG' ms' PO;
  (let T := type of PO in let T := eval hnf in T in
   lazymatch T with
   | ?A /\ _ => tryif is_fp_clause A then (let FP := fresh "FP" in destruct PO as [FP PO]; fp_use FP) else idtac
   | _ => idtac
   end);
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ ?m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (let MIname := fresh "MI" in
       lazymatch goal with H : mem_inv segs _ |- _ => rename H into MIname; try rename MIname into MI end);
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
