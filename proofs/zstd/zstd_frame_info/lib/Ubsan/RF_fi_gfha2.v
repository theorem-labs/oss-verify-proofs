(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge Image Mem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_memcpy Startup_B RF_fi_iface RF_fi_small RF_fi_gfha RF_fi_gfha_d0 RF_fi_gfha_d1 RF_fi_gfha_d2 RF_fi_gfha_d3.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Section S.
  Variables (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : fmem) (S : Z) (bl : list Z) (ZF lo : Z).
  Notation n := (zlen bl).
  Notation sp := (Z_to_bv 64 SP).
  Notation W := [(ZF, ZF + 48); (SP - GFHA_FRAME, SP)].
  Notation POST := (gfha_post ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ZF n lo m).
  Hypothesis BUF : buf_at m S bl.
  Hypothesis NB : n < 2^62.
  Hypothesis LO : lo <= SP - GFHA_FRAME.
  Hypothesis SPH : 0 <= SP < 2^64.
  Hypothesis SEP1 : S + n <= ZF \/ ZF + 48 <= S.
  Hypothesis SEP2 : S + n <= SP - GFHA_FRAME \/ SP <= S.
  Hypothesis SEP3 : ZF + 48 <= SP - GFHA_FRAME \/ SP <= ZF.
  Hypothesis ZA : ZF mod 8 = 0.
  Ltac small_tail := eapply gfha_tail; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; (let HR := fresh in intros HR; exfalso; vm_compute in HR; lia).

  (* [comment removed for export] *)
  Ltac zf_generic :=
    lazymatch goal with
    | CZ : rw_cells _ ?m1 ZF ?cs |- _ =>
        let j := fresh "zj" in let C := fresh "CZ" in
        destruct (rw_cells_forget usegs m1 ZF cs CZ) as [j C]; clear CZ; cbn [cells_size csize Nat.add] in C;
        apply (rw_cells_split_CB usegs _ _ [] 48 j [] [24; 4; 20]%nat) in C; [| reflexivity]; cbn [app mk_CB_cells] in C
    end.
  Ltac exit_tail := zf_generic; small_tail.
  (* [comment removed for export] *)
  Ltac zf_success :=
    lazymatch goal with
    | CZ : rw_cells _ ?m1 ZF [?c0; ?c1; ?c2; ?c3; C4 ?h; ?c5; ?c6; ?c7; ?c8] |- _ =>
        apply (rw_cells_reshape m1 ZF _ [CB 24 (cbytes c0 ++ cbytes c1 ++ cbytes c2 ++ cbytes c3); CB 4 (le4 h);
                                       CB 20 (cbytes c5 ++ cbytes c6 ++ cbytes c7 ++ cbytes c8)]) in CZ;
        [| cbn [cells_wf cell_wf cbytes]; rewrite ?length_app, ?length_le8, ?length_le4; repeat split; reflexivity
         | cbn [cells_bytes cbytes]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity
         | reflexivity ]
    end;
    eapply gfha_tail; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; intros _; eexists; split; [reflexivity| split; lia].
  (* [comment removed for export] *)
  Ltac brr := first [if_true | if_false].
  (* [comment removed for export] *)
  Ltac pose_rds2 a b :=
    let t := eval vm_compute in (Z.ltb a b) in
    lazymatch t with
    | true => pose_rd a; let a' := eval vm_compute in (a + 1) in pose_rds2 a' b
    | false => idtac
    end.
  (* [comment removed for export] *)
  #[using="Type"] Lemma fhtab_read_at : forall m1 k A, mem_inv usegs m1 -> 0 <= k < 8 -> A = PFI_DIDTAB + 8 * k ->
    ov_read_bytes usegs m1 (wa A) 8 = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * k)) FHTAB))).
  Proof. intros m1 k A MI1 Hk ->. apply fhtab_read; assumption. Qed.
  Ltac pose_tab k :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MIx : mem_inv usegs m1 |- _ =>
        let A := eval vm_compute in (PFI_DIDTAB + 8 * k) in
        let H := fresh "TAB" in
        pose proof (fhtab_read_at m1 k A MIx ltac:(lia) ltac:(reflexivity)) as H;
        lazymatch type of H with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in H end
      end
    end.
  (* [comment removed for export] *)
  Ltac gstep Hd Hs Hr Hf E24 E64 :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 77380 => first [ zf_success | exit_tail ]                                   (* [comment removed for export] *)
      | 77636 => zstep; rewrite Hd          (* [comment removed for export] *)
      | 77640 => zstep; rewrite Hs          (* [comment removed for export] *)
      | 77648 => zstep; rewrite E64; try change (Z.b2z true) with 1; try change (Z.b2z false) with 0   (* [comment removed for export] *)
      | 77660 => zstep; try change (Z.b2z (0 <? 1)) with 1; try change (Z.b2z (32 <? 1)) with 0      (* [comment removed for export] *)
      | 77664 => zstep; rewrite E24         (* [comment removed for export] *)
      | 77704 => zstep; let K := fresh "KL" in if_cases K; zify_cond K;            (* [comment removed for export] *)
                 [ zstep; clear_rd; lazymatch type of K with ?Lv <= _ => pose_rds2 4 Lv end | ]
      | 77724 => zstep; cbv beta; lazymatch goal with RB : 0 <= Znth 4 bl < 256 |- _ => rewrite (byte_lit _ RB) end   (* [comment removed for export] *)
      | 77732 => zstep; let K := fresh "KR" in if_cases K; zify_cond K          (* [comment removed for export] *)
      | 77736 => zstep; rewrite Hs          (* [comment removed for export] *)
      | 77744 => zstep; cbv beta; lazymatch goal with RB : 0 <= Znth 5 bl < 256 |- _ => rewrite (byte_lit _ RB) end   (* [comment removed for export] *)
      | 77752 => zstep; let K := fresh "KW" in if_cases K; zify_cond K          (* [comment removed for export] *)
      | 77964 => zstep; rewrite Hd          (* [comment removed for export] *)
      | 77972 => zstep; rewrite Hf          (* [comment removed for export] *)
      | 78244 => zstep; let K := fresh "KB" in if_cases K; clear K               (* [comment removed for export] *)
      | _ => zstep; try brr
      end
    | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 1 "gstep: undecided branch at" pc
    end.

  (* [comment removed for export] *)
  #[using="BUF NB LO SPH SEP1 SEP2 SEP3 ZA"] Lemma gfha_main : main_ok ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S bl ZF lo.
  Proof.
    unfold main_ok, main_at. intros until q19. intros N5 SPOS CZ FR PL ST MU WM MI. unfold GFHA_FRAME in *.
    pose proof (proj2 BUF) as PLR.
    pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof (rw_cells_bound _ _ _ _ CZ) as ZB. cbn [cells_size csize Nat.add] in ZB.
    pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
    Local Ltac2 Set LiaHints.tbl := fun () => "01M0>10512988003.6610642993207.5910642993207.6613140303554.8613906168896.8014204193978.7014204193981.6315098614170.6815534906503.8415534906503.8915534906503.9415658255133.6815658255133.9615878973750.7516075585474.7016538592739.6819589975962.682142410759.86 21920002361.6821922099471.6122736118043.6822736118043.9623594159541.7324063222530.6825870727770.8626437422590.6826437422590.9627463931975.6828458877677.7728458877678.7928463086175.6128465183332.7428465183333.7328465183334.7528465183336.6928465183337.6828465183338.7028465183339.7228465183341.6328465183342.6528465183343.6731143794842.6831143794842.893132576391.84 3132576391.89 3132576391.94 31426431943.683272297910.68 3272297910.96 33903789786.89355734914.68  35852192547.8636944756847.6836944756847.9638953787207.6640428100743.6640428100743.6840428100743.8640428100743.8940428100743.9641863133603.8943158952066.6643929283713.8243929283713.8743929283719.944502176483.68 4502176483.89 45069577535.6745071950103.7148399080583.8949604477442.6849604477442.8954490019650.8956748350663.6856748350663.8959314873579.7159314873579.7259588178608.8359588178609.8259588178609.8759588178615.9461172658147.6861450317115.7261450317118.6563106199869.7763653708231.6864243778586.6865836209410.6867193953379.687065539866.66 8134992339.80 8147615255.68 8147615255.96 00000>00L00Z01<01G01U01c02102202302402c04Y04g05805F05T05d06206@06P06`06n07P07^08@08b09209=09H09S09^09i0:40:?0:J0:U0:`0:k0;60;A0;O0;]0;^0;_0;`0<00<>0<L0<Z0=<0=J0=X0=f0>60>A0>L0>W0>b0>m0?;0?]0?^0?_0?`0?n0@<0@J0@X0@h0AJ0Al0BN0B^0Bn0C;0CH0CS0C^0Ci0D40DB0DP0D^0Dl0E<0EJ0El0F:0FH0FV0GE0I;S3SPH2ZB2FB2HBS3SPH2N52ZB2FBS3SPH2N52ZB2FBS3SPH4SEP14SEP24SEP34LENB2ZB2FB2K8S3SPH2ZB2FBS3SPH2N52ZB2FBS3SPH2N52ZB2FBS3SPH2ZB2FB2HBFFFS3BUF2NB2LO3SPH4SEP14SEP24SEP32N52BB4LENB2ZB2FBS3BUF2NB2LO3SPH4SEP14SEP24SEP32N52BB4LENB2ZB2FB2RB3RB03RB13RB23RB32K83RB43RB53RB63RB72RD3RB83RD03RB93RD14RB103RD24RB11S3SPH2ZB2FB2K8S2NB3SPH2N52ZB2FBS3SPH2ZB2FB2HBS3SPH2ZB2FB2HBS3SPH4SEP32ZB2FBS3SPH2N52ZB2FBS3SPH2N52ZB2FBS3SPH4SEP32ZB2FBS3SPH4SEP32ZB2FBS3SPH2ZB2FB2K8S3SPH4SEP14SEP24SEP32N54LENB2ZB2FBS3SPH2ZB2FB2HBS3SPH4SEP14SEP24SEP32N54LENB2ZB2FBS3SPH4SEP14SEP24SEP34LENB2ZB2FB2K8S3SPH4SEP32ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FB2HBS3SPH2ZB2FB2HBFFFS3SPH4SEP32ZB2FBS3SPH2ZB2FB2HBS3SPH2ZB2FB2HBS3SPH2ZB2FB2HBS3SPH4SEP14SEP24SEP32N54LENB2ZB2FBS3SPH2ZB2FB2HBS3SPH2ZB2FB2HBS3SPH2ZB2FB2HBS3SPH4SEP32ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FB2HBS3SPH4SEP14SEP24SEP32N54LENB2ZB2FBFFFS3SPH2ZB2FB2HBS3SPH2ZB2FB2HBS3SPH2N52ZB2FBS3SPH2N52ZB2FBS3SPH4SEP32ZB2FBS3SPH4SEP14SEP24SEP32N54LENB2ZB2FBS3SPH4SEP14SEP24SEP34LENB2ZB2FB2K8S3SPH4SEP14SEP24SEP34LENB2ZB2FB2K8S3SPH4SEP32ZB2FBS3SPH4SEP32ZB2FBS3SPH2ZB2FB1HS3SPH2ZB2FB1HS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FBS3SPH2ZB2FB2HBS3SPH2N52ZB2FBS3SPH2N52ZB2FBS3SPH2ZB2FB2K8S3SPH4SEP32ZB2FBS3SPH2ZB2FB2HBS3SPH4SEP14SEP24SEP32N54LENB2ZB2FBS3SPH2ZB2FB2HBS3SPH2ZB2FB2HBS3SPH2ZB2FB2K8S3BUF2NB2LO3SPH4SEP14SEP24SEP32N52BB4LENB2ZB2FBS3BUF2NB2LO3SPH4SEP14SEP24SEP32N52BB4LENB2ZB2FB2RB3RB03RB13RB23RB32K83RB43RB53RB63RB72RD3RB83RD03RB93RD14RB103RD24RB11".
do 7 zstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with CZx : rw_cells _ ?m1 ZF _ |- _ =>
      apply (rw_cells_reshape m1 ZF _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                                     C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in CZx;
      [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ] end.
    zstep. if_true. (* [comment removed for export] *)
    zstep. if_cases KN; zify_cond KN; [exfalso; lia|]. (* [comment removed for export] *)
    pose_rd 0. pose_rd 1. pose_rd 2. pose_rd 3. pose_rd 4.
    do 12 zstep. (* [comment removed for export] *)
    zstep. if_cases KM; clear KM.   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      do 4 zstep. if_cases KSK; clear KSK.
      + (* [comment removed for export] *) zstep. zstep. exit_tail.
      + zstep. zstep. if_cases K8; zify_cond K8.
        * (* [comment removed for export] *) exit_tail.
        * (* [comment removed for export] *)
          zstep. rewrite (land7_mod8 ZF ZA). zstep. if_false. zstep. zstep. (* [comment removed for export] *)
          clear_rd. pose_rd 0. pose_rd 1. pose_rd 2. pose_rd 3.
          do 16 zstep. (* [comment removed for export] *)
          zstep. zstep. (* [comment removed for export] *)
          zstep. if_cases KO; zify_cond KO; [exfalso; lia|].
          zstep.
          clear_rd. pose_rd 4. pose_rd 5. pose_rd 6. pose_rd 7.
          do 10 zstep. (* [comment removed for export] *)
          zstep. (* [comment removed for export] *)
          zstep. (* [comment removed for export] *)
          zf_success.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases KO; zify_cond KO; [exfalso; rewrite ?zb_lxor_ones in KO by lia; lia|].
      zstep. zstep. (* [comment removed for export] *) cbv beta.
      lazymatch goal with RB : 0 <= Znth 4 bl < 256 |- _ => rewrite (byte_lit _ RB); pose proof (fhd_decomp _ RB) as DEC end.
      destruct DEC as (Hd & _).
      destruct Hd as [Hd|[Hd|[Hd|Hd]]]; [ eapply dec0 | eapply dec1 | eapply dec2 | eapply dec3 ]; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="BUF NB LO SPH SEP1 SEP2 SEP3 ZA"] Lemma gfha_at_entry : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (zj : list byte),
    rw_cells usegs m ZF [CB 48 zj] -> stk usegs m lo SP -> mem_inv usegs m -> a3 = Z_to_bv 64 0 ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ZF) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFI_GFHA) fc None m (seg_rom usegs)).
  Proof.
    intros. eapply gfha_entry; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. exact gfha_main.
  Qed.
End S.

Theorem gfha_proof : gfha_stmt.
Proof.
  intros until zj. intros BUF NB CZ ZA ST LO SPH SEP1 SEP2 SEP3 MI FMT -> -> ->.
  eapply gfha_at_entry; eassumption.
Qed.

(* [comment removed for export] *)
Theorem gfh_proof : gfh_stmt.
Proof.
  intros until zj. intros BUF NB CZ ZA ST LO SPH SEP1 SEP2 SEP3 MI _ -> -> ->. unfold PFI_GFH.
  zstep. zstep. eapply gfha_at_entry; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. reflexivity.
Qed.
