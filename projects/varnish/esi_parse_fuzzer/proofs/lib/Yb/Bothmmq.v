(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec ShapeAlg SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct Asanoq0 AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothny9 AsanInit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asang2p.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asang2p.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asang2p.

Module Bothv4r.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SumsLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothp5b.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SumsLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothp5b.BSumzok.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition imemcpy_words : list (bv 32) :=
  [W_6a0f4; W_6a0f8; W_6a0fc; W_6a100; W_6a104; W_6a108; W_6a10c; W_6a110; W_6a114].

(* [comment removed for export] *)
Definition imemcpy_clob : list reg := [11; 12; 13; 14].

Section IMEMCPY.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 imemcpy_words.
  Hypothesis HOK : cpyH segs mem0 dst src n bs.

  #[local] Abbreviation MK := (memk mem0 dst bs).
  #[local] Abbreviation B := (b_ bs).
  #[local] Abbreviation CL := (fun r => In r imemcpy_clob).
  Let Hn0 : (0 <= n)%Z := cHn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := cHnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := cHnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at imemcpy_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & _).

  (* [comment removed for export] *)
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk :=
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | apply sb_val_b | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma imemcpy_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = at_ dst n ->
    (0 <= k < n)%Z -> Z.of_nat i = (n - 1 - k)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 12) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
    - (* [comment removed for export] *)
      eexists. split.
      + mlbu C12 D_6a100 k.                       (* [comment removed for export] *)
        msb C16 D_6a104 k.                        (* [comment removed for export] *)
        an C20 D_6a108.                           (* [comment removed for export] *)
        an C24 D_6a10c.                           (* [comment removed for export] *)
        ab_ft C28 D_6a110 ltac:(condz).           (* [comment removed for export] *)
        aret C32 D_6a114 ret.
        replace (k + 1)%Z with n by lia. apply mst_refl.
      + unfold imemcpy_clob. solve_regs_agree.
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1)
                         /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C12 D_6a100 k.
          msb C16 D_6a104 k.
          an C20 D_6a108.
          an C24 D_6a10c.
          ab_tk C28 D_6a110 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold imemcpy_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Theorem imemcpy_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    rewrite <- (memk_n _ _ _ _ _ _ HOK). change mem0 with (MK 0).
    destruct (Z.eq_dec n 0) as [Hz|Hnz].
    - (* [comment removed for export] *)
      eexists. split.
      + ab_tk C0 D_6a0f4 ltac:(condz).            (* [comment removed for export] *)
        aret C32 D_6a114 ret.
        rewrite Hz. apply mst_refl.
      + apply regs_agree_refl.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK 0) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0
                         /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_ft C0 D_6a0f4 ltac:(condz).          (* [comment removed for export] *)
          av C4 D_6a0f8 (at_ dst n) ltac:(apply v_add_at; lia).  (* [comment removed for export] *)
          an C8 D_6a0fc.                          (* [comment removed for export] *)
          apply mst_refl.
        * post; rewrite ?at_0; try reflexivity. unfold imemcpy_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (imemcpy_loop (Z.to_nat (n - 1)) r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End IMEMCPY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition both_imemcpy_entry : word := 0x6a0f4.

Lemma both_imemcpy_code :
  code_at AsanUbsan.M.loaded_segments both_imemcpy_entry 0 imemcpy_words.
Proof. unfold imemcpy_words. code_at_vm. Qed.

Theorem both_imemcpy : forall mem0 (dst src : word) n bs rom regs (ret : word),
  cpyH AsanUbsan.M.loaded_segments mem0 dst src n bs ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs both_imemcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
    /\ regs_agree (fun r => In r imemcpy_clob) regs regs'.
Proof.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite <- (at_0 both_imemcpy_entry).
  apply (imemcpy_run _ _ mem0 dst src n bs rom both_imemcpy_code HOK).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Bothv4r.

Module Bothhsz.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SumsLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothp5b.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SumsLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothp5b.BSumzok.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition memisz_words : list (bv 32) :=
  [W_6a6a0; W_6a6a4; W_6a6a8; W_6a6ac; W_6a6b0; W_6a6b4; W_6a6b8; W_6a6bc;
   W_6a6c0; W_6a6c4; W_6a6c8; W_6a6cc; W_6a6d0; W_6a6d4; W_6a6d8; W_6a6dc;
   W_6a6e0; W_6a6e4; W_6a6e8; W_6a6ec; W_6a6f0; W_6a6f4; W_6a6f8; W_6a6fc;
   W_6a700; W_6a704; W_6a708; W_6a70c; W_6a710; W_6a714; W_6a718; W_6a71c;
   W_6a720; W_6a724; W_6a728; W_6a72c; W_6a730; W_6a734; W_6a738].

(* [comment removed for export] *)
Definition memisz_clob : list reg := [10; 11; 12; 13; 14; 15; 16].
(* [comment removed for export] *)
Definition memisz_clob' : list reg := [1; 2; 10; 11; 12; 13; 14; 15; 16].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_m8 : forall a, (0 <= a < 2 ^ 64)%Z -> Z.land a (2 ^ 64 - 2 ^ 3) = (a - a mod 8)%Z.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 2 ^ 3)%Z with (Z.ldiff (Z.ones 64) (Z.ones 3)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod a (2 ^ 3) ltac:(lia)). change (2 ^ 3)%Z with 8%Z in *. lia.
Qed.

(* [comment removed for export] *)
Lemma v_andi_m8 : forall (a : word) d,
  (0 <= bv_unsigned a + d < 2 ^ 64)%Z ->
  v_andi (at_ a d) (-8) = at_ a (d - (bv_unsigned a + d) mod 8).
Proof.
  intros a d Hd. unfold v_andi, at_. f_equal.
  change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite u_Z2bv by lia. rewrite land_m8 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_all1 : forall segs m n (a : word) b,
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z ->
     rdn segs m x 1 = Some [b]) ->
  rdn segs m a n = Some (repeat b n).
Proof.
  intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  pose proof (Hall a ltac:(lia)) as R. cbn [rdn repeat] in R |- *.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
  injection R as ->.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH (a + 1) b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
    reflexivity.
Qed.

Lemma regs_agree_upd_same : forall (C : regset) regs regs' (r : reg) v,
  regs_agree C regs regs' -> getr regs r = v -> r <> 0 -> regs_agree C regs (regupd regs' r v).
Proof.
  intros C regs regs' r v AG Hv Hnz x Hx.
  destruct (decide (x = r)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply AG, Hx.
Qed.

(* [comment removed for export] *)
Lemma regs_agree_strengthen : forall (l l' : list reg) regs regs',
  regs_agree (fun r => In r l') regs regs' ->
  (forall r, In r l' -> ~ In r l -> getr regs' r = getr regs r) ->
  regs_agree (fun r => In r l) regs regs'.
Proof.
  intros l l' regs regs' AG E r Hr.
  destruct (In_dec (fun x y : reg => decide (x = y)) r l') as [Hin|Hnin].
  - apply E; assumption.
  - apply AG, Hnin.
Qed.

Section MEMISZERO.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem : word -> option byte.
  Variables beg sp : word.
  Variable N : Z.            (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 memisz_words.
  Hypothesis HN : (0 <= N <= 2 ^ 40)%Z.
  Hypothesis Hnw : (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z.
  Hypothesis Hsp : (16 <= bv_unsigned sp)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-8)) 8 = true.
  Hypothesis Hdisj : (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z.
  Hypothesis Hz : forall a : word,
      (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation B := (bv_unsigned beg).
  #[local] Abbreviation Z0 := (Z_to_bv 64 0).
  #[local] Abbreviation CL := (fun r => In r memisz_clob').
  (* [comment removed for export] *)
  Definition dAB : Z := 7 - (B + 7) mod 8.
  Definition dAE : Z := N - (B + N) mod 8.
  (* [comment removed for export] *)
  Definition mem1 (ra : word) : word -> option byte := wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ra).

  Lemma dAB_range : (0 <= dAB <= 7)%Z.
  Proof. unfold dAB. pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). lia. Qed.

  Lemma dAE_range : (N - 7 <= dAE <= N)%Z /\ (0 <= B + dAE)%Z.
  Proof.
    unfold dAE. pose proof (u64_range beg). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
    pose proof (Z.div_mod (B + N) 8 ltac:(lia)). nia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd1 : forall ra j, (0 <= j < N)%Z -> rdn segs (mem1 ra) (at_ beg j) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros ra j Hj. pose proof (u64_range beg). pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?at_u; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
    apply Hz. rewrite at_u; lia.
  Qed.

  Lemma rd8 : forall ra j, (0 <= j)%Z -> (j + 8 <= N)%Z -> rdn segs (mem1 ra) (at_ beg j) 8 = Some (zeros 8).
  Proof.
    intros ra j Hj H8. pose proof (u64_range beg). unfold zeros. apply rdn_all1; [rewrite at_u; cbn; lia|].
    intros x Hx. rewrite at_u in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
    replace x with (at_ beg (bv_unsigned x - B)).
    - apply rd1. lia.
    - unfold at_. rewrite <- (Z_to_bv_bv_unsigned 64 x) at 2. f_equal. lia.
  Qed.

  Lemma rd_ra : forall ra, rdn segs (mem1 ra) (at_ sp (-8)) 8 = Some (word_to_le_bytes 8 ra).
  Proof. intros ra. unfold mem1. apply rdn_wbytes_hit8. pose proof (u64_range sp). rewrite at_u; lia. Qed.

  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at memisz_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56
                    & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & C112
                    & C116 & C120 & C124 & C128 & C132 & C136 & C140 & C144 & C148 & C152 & _).

  (* [comment removed for export] *)
  Ltac mlbu F D :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := Z_to_bv 8 0);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; apply rd1; lia]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac mld F D :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := zeros 8) (v := Z_to_bv 64 0);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; apply rd8; lia
        | reflexivity]
      | step_simpl]; vn.

  Ltac ra_solve :=
    repeat (first [ apply regs_agree_upd; [in_list|]
                  | apply regs_agree_upd_same; [| rwH; rewrite ?at_0; reflexivity | let X := fresh in intros X; discriminate X] ]);
    first [apply regs_agree_refl | assumption].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fin_run : forall regs (ret : word),
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 11 = Z0 ->
    exists regs',
      msteps segs (mkst regs (at_ base 140) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. intros regs ret Hret H2 H11. pose proof (u64_range sp).
    eexists. split; [|split; [|split; [|split]]].
    - an C140 D_6a72c.                            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (v := ret);
          [exact C144 | reflexivity | exact D_6a730
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply rd_ra
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                         (* [comment removed for export] *)
      an C148 D_6a734.                            (* [comment removed for export] *)
      aret C152 D_6a738 ret.
      apply mst_refl.
    - unfold memisz_clob'. solve_regs_agree.
    - gres. reflexivity.
    - gres. rewrite ?at_0. reflexivity.
    - gres. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ep_loop : forall (i : nat) regs (ret : word) q cnt,
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg q -> getr regs 14 = Z_to_bv 64 cnt ->
    (0 <= q)%Z -> (1 <= cnt)%Z -> (q + cnt <= N)%Z -> Z.of_nat i = (cnt - 1)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 120) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. pose proof (u64_range beg) as Hb.
    induction i as [|i IH]; intros regs ret q cnt Hret H2 H11 H12 H14 Hq Hc Hqc Hi.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C120 D_6a718.                      (* [comment removed for export] *)
          av C124 D_6a71c (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).  (* [comment removed for export] *)
          an C128 D_6a720.                        (* [comment removed for export] *)
          an C132 D_6a724.                        (* [comment removed for export] *)
          ab_ft C136 D_6a728 ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. (intros r1; (first [ intro dR_17; dand3 dR_17 as R2 R11 AG | intros (R2 & R11 & AG) ])).
        (first [ pose proof ((fin_run r1 ret Hret R2 R11)) as dR_1; dex1 dR_1 as r2; dand3 dR_1 as RUN AG2 P | pose proof ((fin_run r1 ret Hret R2 R11)) as dR_1; dand4 dR_1 as r2 RUN AG2 P | destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P) ]). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg (q + 1)
                         /\ getr r 14 = Z_to_bv 64 (cnt - 1) /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C120 D_6a718.
          av C124 D_6a71c (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
          an C128 D_6a720.
          an C132 D_6a724.
          ab_tk C136 D_6a728 ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. (intros r1; (first [ intro dR_18; dand5 dR_18 as R2 R11 R12 R14 AG | intros (R2 & R11 & R12 & R14 & AG) ])).
        (first [ pose proof ((IH r1 ret (q + 1)%Z (cnt - 1)%Z Hret R2 R11 R12 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_2; dex1 dR_2 as r2; dand3 dR_2 as RUN AG2 P | pose proof ((IH r1 ret (q + 1)%Z (cnt - 1)%Z Hret R2 R11 R12 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_2; dand4 dR_2 as r2 RUN AG2 P | destruct (IH r1 ret (q + 1)%Z (cnt - 1)%Z Hret R2 R11 R12 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P) ]). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma tail_run : forall regs (ret : word),
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N ->
    exists regs',
      msteps segs (mkst regs (at_ base 108) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. intros regs ret Hret H2 H10 H11 H12 H14.
    pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
    destruct (Z.lt_ge_cases dAE 0) as [Hneg|Hnn].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C108 D_6a70c ltac:(rewrite <- (at_0 beg) at 2; condz).   (* [comment removed for export] *)
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. (intros r1; (first [ intro dR_19; dand3 dR_19 as R2 R11 AG | intros (R2 & R11 & AG) ])).
        (first [ pose proof ((fin_run r1 ret Hret R2 R11)) as dR_3; dex1 dR_3 as r2; dand3 dR_3 as RUN AG2 P | pose proof ((fin_run r1 ret Hret R2 R11)) as dR_3; dand4 dR_3 as r2 RUN AG2 P | destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P) ]). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - destruct (Z.lt_ge_cases dAE N) as [Hlt|Hge].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = Z_to_bv 64 (N - dAE) /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C108 D_6a70c ltac:(rewrite <- (at_0 beg) at 2; condz).  (* [comment removed for export] *)
             ab_ft C112 D_6a710 ltac:(condz).                              (* [comment removed for export] *)
             av C116 D_6a714 (Z_to_bv 64 (N - dAE)) ltac:(unfold v_sub, at_; unorm; f_equal; lia).  (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. (intros r1; (first [ intro dR_20; dand5 dR_20 as R2 R11 R12 R14 AG | intros (R2 & R11 & R12 & R14 & AG) ])).
          (first [ pose proof ((ep_loop (Z.to_nat (N - dAE - 1)) r1 ret dAE (N - dAE) Hret R2 R11 R12 R14
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as r2; dand3 dR_4 as RUN AG2 P | pose proof ((ep_loop (Z.to_nat (N - dAE - 1)) r1 ret dAE (N - dAE) Hret R2 R11 R12 R14
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_4; dand4 dR_4 as r2 RUN AG2 P | destruct (ep_loop (Z.to_nat (N - dAE - 1)) r1 ret dAE (N - dAE) Hret R2 R11 R12 R14
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P) ]). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C108 D_6a70c ltac:(rewrite <- (at_0 beg) at 2; condz).  (* [comment removed for export] *)
             ab_tk C112 D_6a710 ltac:(condz).                              (* [comment removed for export] *)
             apply mst_refl.
          -- post; apply regs_agree_refl.
        * cbv beta. (intros r1; (first [ intro dR_21; dand3 dR_21 as R2 R11 AG | intros (R2 & R11 & AG) ])).
          (first [ pose proof ((fin_run r1 ret Hret R2 R11)) as dR_5; dex1 dR_5 as r2; dand3 dR_5 as RUN AG2 P | pose proof ((fin_run r1 ret Hret R2 R11)) as dR_5; dand4 dR_5 as r2 RUN AG2 P | destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P) ]). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma w_loop : forall (i : nat) regs (ret : word) p,
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N -> getr regs 15 = at_ beg p ->
    (0 <= p)%Z -> (p + 8 <= dAE)%Z -> (Z.of_nat i * 8 = dAE - p - 8)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 92) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
    induction i as [|i IH]; intros regs ret p Hret H2 H10 H11 H12 H14 H15 Hp Hp8 Hi.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
      + eexists. split.
        * mld C92 D_6a6fc.                        (* [comment removed for export] *)
          an C96 D_6a700.                         (* [comment removed for export] *)
          an C100 D_6a704.                        (* [comment removed for export] *)
          ab_ft C104 D_6a708 ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. (intros r1; (first [ intro dR_22; dand6 dR_22 as R2 R10 R11 R12 R14 AG | intros (R2 & R10 & R11 & R12 & R14 & AG) ])).
        (first [ pose proof ((tail_run r1 ret Hret R2 R10 R11 R12 R14)) as dR_6; dex1 dR_6 as r2; dand3 dR_6 as RUN AG2 P | pose proof ((tail_run r1 ret Hret R2 R10 R11 R12 R14)) as dR_6; dand4 dR_6 as r2 RUN AG2 P | destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P) ]). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg (p + 8) /\ regs_agree CL regs r)).
      + eexists. split.
        * mld C92 D_6a6fc.
          an C96 D_6a700.
          an C100 D_6a704.
          ab_tk C104 D_6a708 ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. (intros r1; (first [ intro dR_23; dand7 dR_23 as R2 R10 R11 R12 R14 R15 AG | intros (R2 & R10 & R11 & R12 & R14 & R15 & AG) ])).
        (first [ pose proof ((IH r1 ret (p + 8)%Z Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_7; dex1 dR_7 as r2; dand3 dR_7 as RUN AG2 P | pose proof ((IH r1 ret (p + 8)%Z Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_7; dand4 dR_7 as r2 RUN AG2 P | destruct (IH r1 ret (p + 8)%Z Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P) ]). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mid_run : forall regs (ret : word),
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 14 = at_ beg N -> getr regs 15 = at_ beg dAB ->
    exists regs',
      msteps segs (mkst regs (at_ base 88) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. intros regs ret Hret H2 H10 H11 H12 H14 H15.
    pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
    destruct (Z.lt_ge_cases dAB dAE) as [Hlt|Hge].
    - (* [comment removed for export] *)
      assert (Hi : exists i : nat, (Z.of_nat i * 8 = dAE - dAB - 8)%Z).
      { unfold dAB, dAE in *.
        pose proof (Z.div_mod (B + 7) 8 ltac:(lia)). pose proof (Z.div_mod (B + N) 8 ltac:(lia)).
        pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
        exists (Z.to_nat ((B + N) / 8 - (B + 7) / 8 - 1)). nia. }
      destruct Hi as (i & Hi).
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_ft C88 D_6a6f8 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. (intros r1; (first [ intro dR_24; dand7 dR_24 as R2 R10 R11 R12 R14 R15 AG | intros (R2 & R10 & R11 & R12 & R14 & R15 & AG) ])).
        (first [ pose proof ((w_loop i r1 ret dAB Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) Hi)) as dR_8; dex1 dR_8 as r2; dand3 dR_8 as RUN AG2 P | pose proof ((w_loop i r1 ret dAB Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) Hi)) as dR_8; dand4 dR_8 as r2 RUN AG2 P | destruct (w_loop i r1 ret dAB Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) Hi)
          as (r2 & RUN & AG2 & P) ]). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C88 D_6a6f8 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. (intros r1; (first [ intro dR_25; dand6 dR_25 as R2 R10 R11 R12 R14 AG | intros (R2 & R10 & R11 & R12 & R14 & AG) ])).
        (first [ pose proof ((tail_run r1 ret Hret R2 R10 R11 R12 R14)) as dR_9; dex1 dR_9 as r2; dand3 dR_9 as RUN AG2 P | pose proof ((tail_run r1 ret Hret R2 R10 R11 R12 R14)) as dR_9; dand4 dR_9 as r2 RUN AG2 P | destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P) ]). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pro_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 2 = at_ sp (-16) -> getr regs 10 = beg -> getr regs 11 = Z0 ->
    getr regs 12 = at_ beg dAE -> getr regs 13 = at_ beg (j + 1) -> getr regs 14 = at_ beg N ->
    getr regs 15 = at_ beg dAB ->
    (0 <= j)%Z -> (j < dAB)%Z -> (j < N)%Z -> Z.of_nat i = (Z.min dAB N - 1 - j)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 64) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
    induction i as [|i IH]; intros regs ret j Hret H2 H10 H11 H12 H13 H14 H15 Hj HjA HjN Hi.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (j + 1) dAB) as [HA|HA].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- an C64 D_6a6e0.                      (* [comment removed for export] *)
             mlbu C68 D_6a6e4.                    (* [comment removed for export] *)
             an C72 D_6a6e8.                      (* [comment removed for export] *)
             ab_tk C76 D_6a6ec ltac:(condz).      (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. (intros r1; (first [ intro dR_26; dand7 dR_26 as R2 R10 R11 R12 R14 R15 AG | intros (R2 & R10 & R11 & R12 & R14 & R15 & AG) ])).
          (first [ pose proof ((mid_run r1 ret Hret R2 R10 R11 R12 R14 R15)) as dR_10; dex1 dR_10 as r2; dand3 dR_10 as RUN AG2 P | pose proof ((mid_run r1 ret Hret R2 R10 R11 R12 R14 R15)) as dR_10; dand4 dR_10 as r2 RUN AG2 P | destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P) ]). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- an C64 D_6a6e0.                      (* [comment removed for export] *)
             mlbu C68 D_6a6e4.                    (* [comment removed for export] *)
             an C72 D_6a6e8.                      (* [comment removed for export] *)
             ab_ft C76 D_6a6ec ltac:(condz).      (* [comment removed for export] *)
             an C80 D_6a6f0.                      (* [comment removed for export] *)
             ab_ft C84 D_6a6f4 ltac:(condz).      (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. (intros r1; (first [ intro dR_27; dand7 dR_27 as R2 R10 R11 R12 R14 R15 AG | intros (R2 & R10 & R11 & R12 & R14 & R15 & AG) ])).
          (first [ pose proof ((mid_run r1 ret Hret R2 R10 R11 R12 R14 R15)) as dR_11; dex1 dR_11 as r2; dand3 dR_11 as RUN AG2 P | pose proof ((mid_run r1 ret Hret R2 R10 R11 R12 R14 R15)) as dR_11; dand4 dR_11 as r2 RUN AG2 P | destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P) ]). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 13 = at_ beg (j + 1 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                         /\ regs_agree CL regs r)).
      + eexists. split.
        * an C64 D_6a6e0.
          mlbu C68 D_6a6e4.
          an C72 D_6a6e8.
          ab_ft C76 D_6a6ec ltac:(condz).         (* [comment removed for export] *)
          an C80 D_6a6f0.
          ab_tk C84 D_6a6f4 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. (intros r1; (first [ intro dR_28; dand8 dR_28 as R2 R10 R11 R12 R13 R14 R15 AG | intros (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG) ])).
        (first [ pose proof ((IH r1 ret (j + 1)%Z Hret R2 R10 R11 R12 R13 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_12; dex1 dR_12 as r2; dand3 dR_12 as RUN AG2 P | pose proof ((IH r1 ret (j + 1)%Z Hret R2 R10 R11 R12 R13 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_12; dand4 dR_12 as r2 RUN AG2 P | destruct (IH r1 ret (j + 1)%Z Hret R2 R10 R11 R12 R13 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P) ]). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem mem_is_zero_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
    getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree (fun r => In r memisz_clob) regs regs'
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
  Proof.
    get_code. intros regs ret Hret H1 H2 H10 H11.
    pose proof (u64_range beg) as Hb. pose proof (u64_range sp) as Hs.
    pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 48) (mem1 ret) rom)
             (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                       /\ getr r 13 = Z_to_bv 64 N /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                       /\ regs_agree CL regs r)).
    { eexists. split.
      - an C0 D_6a6a0.                            (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ sp (-8)) (v := ret);
            [exact C4 | reflexivity | exact D_6a6a4
            | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; reflexivity
            | gres; rwH; reflexivity
            | exact Hstk]
          | step_simpl]; change (wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ret)) with (mem1 ret); vn.
                                                  (* [comment removed for export] *)
        an C8 D_6a6a8.                            (* [comment removed for export] *)
        an C12 D_6a6ac.                           (* [comment removed for export] *)
        an C16 D_6a6b0.                           (* [comment removed for export] *)
        an C20 D_6a6b4.                           (* [comment removed for export] *)
        ab_ft C24 D_6a6b8 ltac:(condz).           (* [comment removed for export] *)
        an C28 D_6a6bc.                           (* [comment removed for export] *)
        av C32 D_6a6c0 (at_ beg N) ltac:(apply v_add_at; lia).              (* [comment removed for export] *)
        an C36 D_6a6c4.                           (* [comment removed for export] *)
        av C40 D_6a6c8 (at_ beg dAB) ltac:(rewrite v_andi_m8 by lia; unfold dAB; f_equal; lia).  (* [comment removed for export] *)
        av C44 D_6a6cc (at_ beg dAE) ltac:(rewrite v_andi_m8 by lia; unfold dAE; reflexivity).    (* [comment removed for export] *)
        apply mst_refl.
      - post. unfold memisz_clob'. solve_regs_agree. }
    cbv beta. (intros r0; (first [ intro dR_29; dand8 dR_29 as R2 R10 R11 R12 R13 R14 R15 AG0 | intros (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG0) ])).
    (* [comment removed for export] *)
    enough (G : exists regs',
      msteps segs (mkst r0 (at_ base 48) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret).
    { (first [ dex1 G as r'; dand5 G as RUN AG P10 P2 P1 | dand6 G as r' RUN AG P10 P2 P1 | destruct G as (r' & RUN & AG & P10 & P2 & P1) ]). exists r'. split; [exact RUN|]. split; [|OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption].
      apply (regs_agree_strengthen memisz_clob memisz_clob'); [exact AG|].
      intros r Hr Hnr. unfold memisz_clob', memisz_clob in *. cbn [In] in Hr.
      destruct Hr as [<-|[<-|Hr]]; [rewrite P1, H1; reflexivity | rewrite P2, H2; reflexivity |].
      exfalso. apply Hnr. cbn [In]. tauto. }
    destruct (Z.eq_dec dAB 0) as [HA0|HA0].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C48 D_6a6d0 ltac:(rewrite <- (at_0 beg) at 1; condz).   (* [comment removed for export] *)
          apply mst_refl.
        * post; exact AG0.
      + cbv beta. (intros r1; (first [ intro dR_30; dand7 dR_30 as S2 S10 S11 S12 S14 S15 AG | intros (S2 & S10 & S11 & S12 & S14 & S15 & AG) ])).
        (first [ pose proof ((mid_run r1 ret Hret S2 S10 S11 S12 S14 S15)) as dR_14; dex1 dR_14 as r2; dand3 dR_14 as RUN AG2 P | pose proof ((mid_run r1 ret Hret S2 S10 S11 S12 S14 S15)) as dR_14; dand4 dR_14 as r2 RUN AG2 P | destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P) ]). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - destruct (Z.eq_dec N 0) as [HN0|HN0].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C48 D_6a6d0 ltac:(rewrite <- (at_0 beg) at 1; condz).  (* [comment removed for export] *)
             ab_tk C52 D_6a6d4 ltac:(condz).                              (* [comment removed for export] *)
             apply mst_refl.
          -- post; exact AG0.
        * cbv beta. (intros r1; (first [ intro dR_31; dand7 dR_31 as S2 S10 S11 S12 S14 S15 AG | intros (S2 & S10 & S11 & S12 & S14 & S15 & AG) ])).
          (first [ pose proof ((mid_run r1 ret Hret S2 S10 S11 S12 S14 S15)) as dR_15; dex1 dR_15 as r2; dand3 dR_15 as RUN AG2 P | pose proof ((mid_run r1 ret Hret S2 S10 S11 S12 S14 S15)) as dR_15; dand4 dR_15 as r2 RUN AG2 P | destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P) ]). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 13 = at_ beg (0 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                           /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C48 D_6a6d0 ltac:(rewrite <- (at_0 beg) at 1; condz).  (* [comment removed for export] *)
             ab_ft C52 D_6a6d4 ltac:(condz).                              (* [comment removed for export] *)
             an C56 D_6a6d8.                                              (* [comment removed for export] *)
             an C60 D_6a6dc.                                              (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. ra_chain.
        * cbv beta. (intros r1; (first [ intro dR_32; dand8 dR_32 as S2 S10 S11 S12 S13 S14 S15 AG | intros (S2 & S10 & S11 & S12 & S13 & S14 & S15 & AG) ])).
          (first [ pose proof ((pro_loop (Z.to_nat (Z.min dAB N - 1)) r1 ret 0 Hret S2 S10 S11 S12 S13 S14 S15
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_16; dex1 dR_16 as r2; dand3 dR_16 as RUN AG2 P | pose proof ((pro_loop (Z.to_nat (Z.min dAB N - 1)) r1 ret 0 Hret S2 S10 S11 S12 S13 S14 S15
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_16; dand4 dR_16 as r2 RUN AG2 P | destruct (pro_loop (Z.to_nat (Z.min dAB N - 1)) r1 ret 0 Hret S2 S10 S11 S12 S13 S14 S15
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P) ]). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.
End MEMISZERO.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma slot_at : forall sp : word, (16 <= bv_unsigned sp)%Z ->
  at_ sp (-8) = Z_to_bv 64 (bv_unsigned sp - 8).
Proof. intros sp Hsp. unfold at_. f_equal; lia. Qed.

Theorem mem_is_zero_summary : forall segs (base : word) mem (beg sp : word) N rom regs (ret : word),
  code_at segs base 0 memisz_words ->
  (0 <= N <= 2 ^ 40)%Z ->
  (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  store_ok segs mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
  (forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
     rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
  exists regs',
    msteps segs (mkst regs base mem rom)
                (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ regs_agree (fun r => In r memisz_clob) regs regs'
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
  intros segs base mem beg sp N rom regs ret HC HN Hnw Hsp Hstk Hdisj Hz.
  rewrite <- (slot_at sp Hsp) in Hstk |- *. rewrite <- (at_0 base).
  apply (mem_is_zero_run segs base mem beg sp N rom HC HN Hnw Hsp Hstk Hdisj Hz).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition both_mem_is_zero_entry : word := 0x6a6a0.

Lemma both_mem_is_zero_code :
  code_at AsanUbsan.M.loaded_segments both_mem_is_zero_entry 0 memisz_words.
Proof. unfold memisz_words. code_at_vm. Qed.

Theorem both_mem_is_zero : forall mem (beg sp : word) N rom regs (ret : word),
  (0 <= N <= 2 ^ 40)%Z ->
  (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
  (16 <= bv_unsigned sp)%Z ->
  store_ok AsanUbsan.M.loaded_segments mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
  (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
  (forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
     rdn AsanUbsan.M.loaded_segments mem a 1 = Some [Z_to_bv 8 0]) ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 N ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs both_mem_is_zero_entry mem rom)
           (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ regs_agree (fun r => In r memisz_clob) regs regs'
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret.
Proof.
  intros mem beg sp N rom regs ret.
  apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret both_mem_is_zero_code).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Bothhsz.

Module Bothtil.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk WalkTac MmapSim RefMocc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Memsalo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Both2uj Bothszu.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
#[local] Ltac solve_incl :=
  let x := fresh "x" in let H := fresh "H" in
  intros x H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [cbn [In]; repeat first [left; reflexivity | right] |]);
  destruct H.

Section Summary.
  Variable mem0 : word -> option byte.
  Variables d cv ret : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ret.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
  #[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).

  (* [comment removed for export] *)
  #[local] Ltac cover L' :=
    apply (cfill_full_chain mem0 d n (cbyte cv) Hn Hnw _ L');
    [ unfold L2, L6, L8, LB, LC, LD; solve_incl
    | cbn [ms_chain]; lia ].

  Theorem memset_summary : forall regs,
    getr regs 10 = d -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    exists regs',
      msteps MSEGS (mkst regs (Z_to_bv 64 ms_base) mem0 rom)
                   (mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
      /\ getr regs' 10 = d /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1.
    pose proof (u64_range d) as Hd.
    rewrite <- (at_0 d) in H10.
    replace (Z_to_bv 64 ms_base) with (PC 0) by (f_equal; lia).
    replace (mkst regs (PC 0) mem0 rom) with (mkst regs (PC 0) (CF []) rom) by (rewrite cfill_nil; reflexivity).
    (* [comment removed for export] *)
    assert (FIN : forall regs' (M : word -> option byte),
              M = wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n)) ->
              msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret M rom) ->
              getr regs' 10 = at_ d 0 -> ms_agree regs regs' ->
              exists regs'',
                msteps MSEGS (mkst regs (PC 0) (CF []) rom)
                       (mkst regs'' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
                /\ getr regs'' 10 = d /\ ms_agree regs regs'').
    { intros regs' M -> RUN P10 AG. exists regs'. rewrite at_0 in P10. auto. }
    destruct (Z.lt_ge_cases n 9) as [Hsmall|Hn9].
    { (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      { (first [ pose proof ((A_exit0 mem0 d cv ret n rom Hn Hret regs H10 H11 H12 H1 Hz)) as dR_1; dex1 dR_1 as r1; dand3 dR_1 as RUN P10 AG | pose proof ((A_exit0 mem0 d cv ret n rom Hn Hret regs H10 H11 H12 H1 Hz)) as dR_1; dand4 dR_1 as r1 RUN P10 AG | destruct (A_exit0 mem0 d cv ret n rom Hn Hret regs H10 H11 H12 H1 Hz) as (r1 & RUN & P10 & AG) ]).
        eapply (FIN r1); try eassumption.
        rewrite cfill_nil. rewrite Hz. reflexivity. }
      destruct (Z.lt_ge_cases n 3) as [H3|H3].
      { (first [ pose proof ((A_exit2 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia))) as dR_2; dex1 dR_2 as r1; dand3 dR_2 as RUN P10 AG | pose proof ((A_exit2 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia))) as dR_2; dand4 dR_2 as r1 RUN P10 AG | destruct (A_exit2 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG) ]).
        eapply (FIN r1); try eassumption. cover ([(0,1); (n-1,1)]%Z). }
      destruct (Z.lt_ge_cases n 7) as [H7|H7].
      { (first [ pose proof ((A_exit6 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia))) as dR_3; dex1 dR_3 as r1; dand3 dR_3 as RUN P10 AG | pose proof ((A_exit6 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia))) as dR_3; dand4 dR_3 as r1 RUN P10 AG | destruct (A_exit6 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG) ]).
        eapply (FIN r1); try eassumption. cover ([(0,1); (1,1); (2,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
      (first [ pose proof ((A_exit8 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia))) as dR_4; dex1 dR_4 as r1; dand3 dR_4 as RUN P10 AG | pose proof ((A_exit8 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia))) as dR_4; dand4 dR_4 as r1 RUN P10 AG | destruct (A_exit8 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG) ]).
      eapply (FIN r1); try eassumption.
      cover ([(0,1); (1,1); (2,1); (3,1); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    (* [comment removed for export] *)
    (first [ pose proof ((A_cont mem0 d cv ret n rom Hn Hnw Hok regs H10 H11 H12 H1 Hn9)) as dR_5; dex1 dR_5 as r1; dand8 dR_5 as RUN1 Q10 Q11 Q12 Q13 Q15 Q1 AG1 | pose proof ((A_cont mem0 d cv ret n rom Hn Hnw Hok regs H10 H11 H12 H1 Hn9)) as dR_5; dand9 dR_5 as r1 RUN1 Q10 Q11 Q12 Q13 Q15 Q1 AG1 | destruct (A_cont mem0 d cv ret n rom Hn Hnw Hok regs H10 H11 H12 H1 Hn9)
      as (r1 & RUN1 & Q10 & Q11 & Q12 & Q13 & Q15 & Q1 & AG1) ]).
    (* [comment removed for export] *)
    set (k := ((- bv_unsigned d) mod 4)%Z).
    pose proof (neg_mod4_range (bv_unsigned d)) as Hk. fold k in Hk.
    pose proof (negw_and3 d) as Hkv. fold k in Hkv.
    set (n1 := (n - k - (n - k) mod 4)%Z).
    set (m1 := ((n - k) / 4)%Z).
    pose proof (Z.div_mod (n - k) 4 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (n - k) 4 ltac:(lia)) as Hmb.
    assert (Hm1 : (4 * m1 = n1)%Z) by (subst n1 m1; lia).
    assert (Hn1 : (n - k - 3 <= n1 <= n - k)%Z) by (subst n1; lia).
    pose proof (andi_m4 (n - k) ltac:(lia)) as Hn1v. fold n1 in Hn1v.
    clearbody n1 m1. clear Hdm Hmb.
    destruct (Z.lt_ge_cases n1 9) as [HB|HB].
    { (* [comment removed for export] *)
      (first [ pose proof ((B_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)) as dR_6; dex1 dR_6 as r2; dand3 dR_6 as RUN2 P10 AG2 | pose proof ((B_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)) as dR_6; dand4 dR_6 as r2 RUN2 P10 AG2 | destruct (B_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
        as (r2 & RUN2 & P10 & AG2) ]).
      eapply (FIN r2); [| eapply msteps_trans; [exact RUN1 | exact RUN2] | exact P10 | eapply ms_agree_trans; eassumption].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+n1-4,4); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    (first [ pose proof ((B_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)) as dR_7; dex1 dR_7 as r2; dand8 dR_7 as RUN2 S10 S11 S12 S13 S14 S1 AG2 | pose proof ((B_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)) as dR_7; dand9 dR_7 as r2 RUN2 S10 S11 S12 S13 S14 S1 AG2 | destruct (B_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
      as (r2 & RUN2 & S10 & S11 & S12 & S13 & S14 & S1 & AG2) ]).
    destruct (Z.lt_ge_cases n1 25) as [HC|HC].
    { (first [ pose proof ((C_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 ltac:(lia) HC)) as dR_8; dex1 dR_8 as r3; dand3 dR_8 as RUN3 P10 AG3 | pose proof ((C_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 ltac:(lia) HC)) as dR_8; dand4 dR_8 as r3 RUN3 P10 AG3 | destruct (C_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 ltac:(lia) HC)
        as (r3 & RUN3 & P10 & AG3) ]).
      eapply (FIN r3); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]
                       | exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
              (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    (first [ pose proof ((C_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 HC)) as dR_9; dex1 dR_9 as r3; dand8 dR_9 as RUN3 T10 T11 T12 T13 T14 T1 AG3 | pose proof ((C_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 HC)) as dR_9; dand9 dR_9 as r3 RUN3 T10 T11 T12 T13 T14 T1 AG3 | destruct (C_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 HC)
      as (r3 & RUN3 & T10 & T11 & T12 & T13 & T14 & T1 & AG3) ]).
    (first [ pose proof ((andi_4_cases (at_ d k))) as dR_10; dex1 dR_10 as s4; destruct dR_10 as [Hs4v Hs4] | pose proof ((andi_4_cases (at_ d k))) as dR_10; dand3 dR_10 as s4 Hs4v Hs4 | destruct (andi_4_cases (at_ d k)) as (s4 & Hs4v & Hs4) ]).
    destruct (Z.lt_ge_cases (n1 - s4 - 24) 32) as [HD|HD].
    { (first [ pose proof ((D_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)) as dR_11; dex1 dR_11 as r4; dand3 dR_11 as RUN4 P10 AG4 | pose proof ((D_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)) as dR_11; dand4 dR_11 as r4 RUN4 P10 AG4 | destruct (D_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
        as (r4 & RUN4 & P10 & AG4) ]).
      eapply (FIN r4); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
                            eapply msteps_trans; [exact RUN3 | exact RUN4]]]
                       | exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
              (k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
              (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    (first [ pose proof ((D_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)) as dR_12; dex1 dR_12 as r4; dand8 dR_12 as RUN4 U10 U11 U12 U14 U15 U1 AG4 | pose proof ((D_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)) as dR_12; dand9 dR_12 as r4 RUN4 U10 U11 U12 U14 U15 U1 AG4 | destruct (D_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
      as (r4 & RUN4 & U10 & U11 & U12 & U14 & U15 & U1 & AG4) ]).
    (first [ pose proof ((E_run mem0 d cv ret n rom k n1 s4 Hs4 r4 (LD n k n1 s4) U10 U11 U12 U14 U15 U1 Hn9 ltac:(lia))) as dR_13; dex1 dR_13 as r5; dand8 dR_13 as RUN5 V10 V11 V12 V13 V14 V1 AG5 | pose proof ((E_run mem0 d cv ret n rom k n1 s4 Hs4 r4 (LD n k n1 s4) U10 U11 U12 U14 U15 U1 Hn9 ltac:(lia))) as dR_13; dand9 dR_13 as r5 RUN5 V10 V11 V12 V13 V14 V1 AG5 | destruct (E_run mem0 d cv ret n rom k n1 s4 Hs4 r4 (LD n k n1 s4) U10 U11 U12 U14 U15 U1 Hn9 ltac:(lia))
      as (r5 & RUN5 & V10 & V11 & V12 & V13 & V14 & V1 & AG5) ]).
    (* [comment removed for export] *)
    set (r := (n1 - s4 - 24)%Z) in *.
    set (q := Z.to_nat (r / 32 - 1)).
    assert (Hq : (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod r 32 ltac:(lia)). pose proof (Z.mod_pos_bound r 32 ltac:(lia)). lia. }
    (first [ pose proof ((loop_run mem0 d cv ret n rom Hnw Hok q r5 (LD n k n1 s4) (k + s4 + 24)%Z r
                V10 V11 V12 V13 V14 V1 ltac:(lia) ltac:(lia) Hq)) as dR_14; dex1 dR_14 as r6; dand4 dR_14 as RUN6 W10 W1 AG6 | pose proof ((loop_run mem0 d cv ret n rom Hnw Hok q r5 (LD n k n1 s4) (k + s4 + 24)%Z r
                V10 V11 V12 V13 V14 V1 ltac:(lia) ltac:(lia) Hq)) as dR_14; dand5 dR_14 as r6 RUN6 W10 W1 AG6 | destruct (loop_run mem0 d cv ret n rom Hnw Hok q r5 (LD n k n1 s4) (k + s4 + 24)%Z r
                V10 V11 V12 V13 V14 V1 ltac:(lia) ltac:(lia) Hq)
      as (r6 & RUN6 & W10 & W1 & AG6) ]).
    (first [ pose proof ((ret_run ret rom Hret r6 (CF (((k + s4 + 24)%Z, (32 * (Z.of_nat q + 1))%Z) :: LD n k n1 s4)) W1)) as dR_15; dex1 dR_15 as r7; destruct dR_15 as [RUN7 ->] | pose proof ((ret_run ret rom Hret r6 (CF (((k + s4 + 24)%Z, (32 * (Z.of_nat q + 1))%Z) :: LD n k n1 s4)) W1)) as dR_15; dand3 dR_15 as r7 RUN7 -> | destruct (ret_run ret rom Hret r6 (CF (((k + s4 + 24)%Z, (32 * (Z.of_nat q + 1))%Z) :: LD n k n1 s4)) W1)
      as (r7 & RUN7 & ->) ]).
    eapply (FIN r6); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
                          eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 |
                          eapply msteps_trans; [exact RUN5 | eapply msteps_trans; [exact RUN6 | exact RUN7]]]]]]
                     | exact W10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
    cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
            (k+s4+24, 32 * (Z.of_nat q + 1));
            (k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
            (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z).
  Qed.

End Summary.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ms_entry : word := ltac:(let l := word_lit (Z_to_bv 64 ms_base) in exact l).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End Bothtil.

Module Bothaek.
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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk WalkTac MmapSim RefMocc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Record mcH (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := MCH {
  Hn : (0 <= n < 2 ^ 64)%Z;
  Hlen : length bs = Z.to_nat n;
  Hsrc : rdn BSEGS mem0 src (length bs) = Some bs;
  Hdst : store_ok BSEGS mem0 dst (length bs) = true;
  Hdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  Hnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MC.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  Let Hn := Hn _ _ _ _ _ HOK.
  Let Hlen := Hlen _ _ _ _ _ HOK.
  Let Hsrc := Hsrc _ _ _ _ _ HOK.
  Let Hdst := Hdst _ _ _ _ _ HOK.
  Let Hdisj := Hdisj _ _ _ _ _ HOK.
  Let Hnws := Hnws _ _ _ _ _ HOK.
  Let Hnwd := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).
  (* [comment removed for export] *)
  Definition sb_ (j : Z) (m : nat) : list byte := sub bs (Z.to_nat j) m.
  (* [comment removed for export] *)
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).

  Lemma lenZ : Z.of_nat (length bs) = n.
  Proof. rewrite Hlen. lia. Qed.

  (* [comment removed for export] *)

  Lemma memk_n : memk n = wbytes mem0 dst bs.
  Proof. unfold memk. rewrite <- Hlen, firstn_all. reflexivity. Qed.

  Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z -> length (sb_ j m) = m.
  Proof. intros j m Hj Hm. unfold sb_. apply sub_length. rewrite Hlen. lia. Qed.

  (* [comment removed for export] *)
  Lemma rd_src : forall k j m,
      (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      rdn BSEGS (memk k) (at_ src j) m = Some (sb_ j m).
  Proof.
    intros k j m Hk Hj Hm. unfold memk, sb_.
    pose proof (u64_range src). pose proof (u64_range dst).
    destruct m as [|m'].
    { cbn. unfold sub. cbn. reflexivity. }
    rewrite rdn_wbytes_out.
    - replace (at_ src j) with (at_ src (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
      apply (rdn_sub BSEGS mem0 (length bs)); [exact Hsrc | rewrite Hlen; lia].
    - rewrite length_firstn, Hlen, at_u; lia.
    - rewrite at_u; lia.
    - rewrite length_firstn, Hlen. lia.
  Qed.

  Lemma rd_src1 : forall k j,
      (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
      rdn BSEGS (memk k) (at_ src j) 1 = Some [b_ j].
  Proof.
    intros k j Hk Hj H1. rewrite (rd_src k j 1) by lia. unfold sb_, b_.
    rewrite sub_nth; [reflexivity | rewrite Hlen; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma wr_dst : forall k j m,
      (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
      store_ok BSEGS (memk k) (at_ dst j) m = true.
  Proof.
    intros k j m Hj Hm. unfold memk.
    apply (store_ok_at BSEGS mem0 dst (length bs)); try assumption; rewrite ?lenZ; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma memk_extend : forall k l m,
      (0 <= k)%Z -> (k + Z.of_nat m <= n)%Z -> l = sb_ k m ->
      wbytes (memk k) (at_ dst k) l = memk (k + Z.of_nat m).
  Proof.
    intros k l m Hk Hm ->. unfold memk, sb_.
    replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
  Qed.

  Lemma memk_extend1 : forall k (b : byte),
      (0 <= k)%Z -> (k + 1 <= n)%Z -> b = b_ k ->
      wbytes (memk k) (at_ dst k) [b] = memk (k + 1).
  Proof.
    intros k b Hk H1 ->.
    replace (k + 1)%Z with (k + Z.of_nat 1)%Z by lia.
    rewrite <- (memk_extend k (sb_ k 1) 1); try lia; [|reflexivity].
    unfold sb_, b_. rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sb4_split : forall j (q : nat), (0 <= j)%Z -> (q <= 4)%nat ->
      sb_ j 4 = sb_ j q ++ sb_ (j + Z.of_nat q) (4 - q).
  Proof.
    intros j q Hj Hq. unfold sb_.
    replace 4%nat with (q + (4 - q))%nat at 1 by lia. rewrite sub_split. f_equal. f_equal. lia.
  Qed.

  Lemma skipn_sb : forall j (q m : nat), (0 <= j)%Z ->
      skipn q (sb_ j m) = sb_ (j + Z.of_nat q) (m - q).
  Proof.
    intros j q m Hj. unfold sb_, sub. rewrite skipn_firstn_comm, <- skipn_add. f_equal. f_equal. lia.
  Qed.

  Lemma firstn_sb : forall j (q m : nat), (q <= m)%nat -> firstn q (sb_ j m) = sb_ j q.
  Proof. intros j q m Hq. unfold sb_, sub. rewrite firstn_firstn. f_equal. lia. Qed.

  (* [comment removed for export] *)
  Lemma merge_sb : forall j (q : nat) (v : word),
      (0 <= j)%Z -> (j + 8 <= n)%Z -> (1 <= q <= 3)%nat ->
      v = v_or (v_slli (LWv (sb_ (j + 4) 4)) (32 - 8 * Z.of_nat q)) (v_srliw (LWv (sb_ j 4)) (8 * Z.of_nat q)) ->
      word_to_le_bytes 4 v = sb_ (j + Z.of_nat q) 4.
  Proof.
    intros j q v Hj H8 Hq Hv.
    rewrite (sw_bytes_merge (sb_ j 4) (sb_ (j + 4) 4) q v); try (apply sb_len; lia); try assumption.
    rewrite skipn_sb, firstn_sb by lia.
    rewrite (sb4_split (j + Z.of_nat q) (4 - q)) by lia.
    f_equal. f_equal; lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word BSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step BSEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) (memk k) rom).
  Proof.
    intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_src1; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_lw : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word BSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 4 <= n)%Z ->
    RiscvSemantics.step BSEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LWv (sb_ j 4))) (v_addi pc 4) (memk k) rom).
  Proof.
    intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj4.
    eapply step_lw; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rd_src k j 4); lia.
    - symmetry. apply u_lez4. apply sb_len; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) k k0 (v : word),
    fetch_word BSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b_ k ->
    (0 <= k)%Z -> (k + 1 <= n)%Z ->
    RiscvSemantics.step BSEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memk (k + 1)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
    rewrite <- (memk_extend1 k (b_ k)) by (lia || reflexivity).
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_sw : forall regs pc rom w rs1 rs2 (imm : bv 12) k k0 (v : word),
    fetch_word BSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 4 v = sb_ k 4 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    RiscvSemantics.step BSEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst regs (v_addi pc 4) (memk (k + 4)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk4.
    replace (k + 4)%Z with (k + Z.of_nat 4)%Z by lia.
    rewrite <- (memk_extend k (sb_ k 4) 4) by (lia || reflexivity).
    rewrite <- Hb.
    eapply step_sw_at; [exact Hf | exact He | exact Hd | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sw_val_plain : forall k, (0 <= k)%Z -> (k + 4 <= n)%Z ->
    word_to_le_bytes 4 (LWv (sb_ k 4)) = sb_ k 4.
  Proof. intros k Hk H4. apply sw_bytes_LWv. apply sb_len; lia. Qed.

  (* [comment removed for export] *)
  Lemma sb_val_plain : forall k, Z_to_bv 8 (bv_unsigned (LBv (b_ k))) = b_ k.
  Proof. intros k. apply sb_byte_LBv. Qed.

  Lemma sb_val_srli : forall j (q : nat), (0 <= j)%Z -> (j + 4 <= n)%Z -> (q <= 3)%nat ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) (8 * Z.of_nat q))) = b_ (j + Z.of_nat q).
  Proof.
    intros j q Hj H4 Hq. rewrite sb_byte_srli_LWv; [| apply sb_len; lia | exact Hq].
    unfold sb_, b_, sub.
    rewrite nth_firstn. replace (q <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_skipn. f_equal. lia.
  Qed.

  Lemma sb_val_word0 : forall j, (0 <= j)%Z -> (j + 4 <= n)%Z ->
    Z_to_bv 8 (bv_unsigned (LWv (sb_ j 4))) = b_ j.
  Proof.
    intros j Hj H4.
    pose proof (sb_val_srli j 0 Hj H4 ltac:(lia)) as E.
    rewrite Z.add_0_r in E. rewrite <- E. f_equal. f_equal.
    unfold v_srli. rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  Lemma merge_s16 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 16) (v_srliw (LWv (sb_ j1 4)) 16) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 2)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 2)%Z with (j1 + Z.of_nat 2)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma merge_s8 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 24) (v_srliw (LWv (sb_ j1 4)) 8) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 1)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 1)%Z with (j1 + Z.of_nat 1)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma merge_s24 : forall (v : word) j1 j2 k,
      v = v_or (v_slli (LWv (sb_ j2 4)) 8) (v_srliw (LWv (sb_ j1 4)) 24) ->
      (j2 = j1 + 4)%Z -> (k = j1 + 3)%Z -> (0 <= j1)%Z -> (j1 + 8 <= n)%Z ->
      word_to_le_bytes 4 v = sb_ k 4.
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 3)%Z with (j1 + Z.of_nat 3)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  Lemma sb_val_srli8 : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j + 1)%Z ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) 8)) = b_ k.
  Proof.
    intros j k Hj H4 ->. replace (j + 1)%Z with (j + Z.of_nat 1)%Z by lia.
    rewrite <- (sb_val_srli j 1) by lia. reflexivity.
  Qed.

  Lemma sb_val_srli16 : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j + 2)%Z ->
    Z_to_bv 8 (bv_unsigned (v_srli (LWv (sb_ j 4)) 16)) = b_ k.
  Proof.
    intros j k Hj H4 ->. replace (j + 2)%Z with (j + Z.of_nat 2)%Z by lia.
    rewrite <- (sb_val_srli j 2) by lia. reflexivity.
  Qed.

  Lemma sb_val_word0' : forall j k, (0 <= j)%Z -> (j + 4 <= n)%Z -> (k = j)%Z ->
    Z_to_bv 8 (bv_unsigned (LWv (sb_ j 4))) = b_ k.
  Proof. intros j k Hj H4 ->. apply sb_val_word0; lia. Qed.

End MC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.

(* [comment removed for export] *)
Ltac mnorm := gres; imm_norm; rewrite ?v_addi_0; rwH; rewrite ?at_addi; vals_lit.

(* [comment removed for export] *)
Ltac cond_lia :=
  rwH; unfold c_ltu, c_eq, bv_ltu, bv_eqb; imm_norm; unorm;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq ]; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_andi : forall (x : word) imm, (0 <= imm < 2 ^ 64)%Z ->
  bv_unsigned (v_andi x imm) = Z.land (bv_unsigned x) imm.
Proof.
  intros x imm Hi. unfold v_andi. rewrite Z_to_bv_unsigned.
  replace (bv_wrap 64 imm) with imm by (symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2^64)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. apply Z_land_range; [apply u64_range|lia].
Qed.

Lemma land_3 : forall a, (0 <= a)%Z -> Z.land a 3 = (a mod 4)%Z.
Proof. intros a Ha. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bits_lt32 : forall m, (0 <= m < 32)%Z ->
  (Z.land m 16 = 0 \/ Z.land m 16 = 16)%Z /\ (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z /\
  (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z /\ (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z /\
  (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z /\
  (m = Z.land m 16 + Z.land m 8 + Z.land m 4 + Z.land m 2 + Z.land m 1)%Z.
Proof.
  intros m Hm.
  assert (E : exists k : nat, m = Z.of_nat k /\ (k < 32)%nat).
  { exists (Z.to_nat m). split; lia. }
  destruct E as (k & -> & Hk).
  do 32 (destruct k as [|k]; [vm_compute; intuition lia|]). lia.
Qed.

(* [comment removed for export] *)
End Bothaek.

Module Bothh6z.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a1b8c : bv 32 := 0x0035f693.
Lemma F_a1b8c : fetch_word AsanUbsan.M.loaded_segments (0xa1b8c : word) = Some W_a1b8c.
Proof. vm_refl. Qed.
Lemma D_a1b8c : decode_any W_a1b8c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1b90 : bv 32 := 0x10068863.
Lemma F_a1b90 : fetch_word AsanUbsan.M.loaded_segments (0xa1b90 : word) = Some W_a1b90.
Proof. vm_refl. Qed.
Lemma D_a1b90 : decode_any W_a1b90 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1b94 : bv 32 := 0x02060e63.
Lemma F_a1b94 : fetch_word AsanUbsan.M.loaded_segments (0xa1b94 : word) = Some W_a1b94.
Proof. vm_refl. Qed.
Lemma D_a1b94 : decode_any W_a1b94 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1b98 : bv 32 := 0x00158713.
Lemma F_a1b98 : fetch_word AsanUbsan.M.loaded_segments (0xa1b98 : word) = Some W_a1b98.
Proof. vm_refl. Qed.
Lemma D_a1b98 : decode_any W_a1b98 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1b9c : bv 32 := 0x00100793.
Lemma F_a1b9c : fetch_word AsanUbsan.M.loaded_segments (0xa1b9c : word) = Some W_a1b9c.
Proof. vm_refl. Qed.
Lemma D_a1b9c : decode_any W_a1b9c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ba0 : bv 32 := 0x00050693.
Lemma F_a1ba0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ba0 : word) = Some W_a1ba0.
Proof. vm_refl. Qed.
Lemma D_a1ba0 : decode_any W_a1ba0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ba4 : bv 32 := 0x0005c883.
Lemma F_a1ba4 : fetch_word AsanUbsan.M.loaded_segments (0xa1ba4 : word) = Some W_a1ba4.
Proof. vm_refl. Qed.
Lemma D_a1ba4 : decode_any W_a1ba4 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ba8 : bv 32 := 0x00060813.
Lemma F_a1ba8 : fetch_word AsanUbsan.M.loaded_segments (0xa1ba8 : word) = Some W_a1ba8.
Proof. vm_refl. Qed.
Lemma D_a1ba8 : decode_any W_a1ba8 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bac : bv 32 := 0x00158593.
Lemma F_a1bac : fetch_word AsanUbsan.M.loaded_segments (0xa1bac : word) = Some W_a1bac.
Proof. vm_refl. Qed.
Lemma D_a1bac : decode_any W_a1bac = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bb0 : bv 32 := 0x00377293.
Lemma F_a1bb0 : fetch_word AsanUbsan.M.loaded_segments (0xa1bb0 : word) = Some W_a1bb0.
Proof. vm_refl. Qed.
Lemma D_a1bb0 : decode_any W_a1bb0 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bb4 : bv 32 := 0x01168023.
Lemma F_a1bb4 : fetch_word AsanUbsan.M.loaded_segments (0xa1bb4 : word) = Some W_a1bb4.
Proof. vm_refl. Qed.
Lemma D_a1bb4 : decode_any W_a1bb4 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bb8 : bv 32 := 0x00168693.
Lemma F_a1bb8 : fetch_word AsanUbsan.M.loaded_segments (0xa1bb8 : word) = Some W_a1bb8.
Proof. vm_refl. Qed.
Lemma D_a1bb8 : decode_any W_a1bb8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bbc : bv 32 := 0xfff60613.
Lemma F_a1bbc : fetch_word AsanUbsan.M.loaded_segments (0xa1bbc : word) = Some W_a1bbc.
Proof. vm_refl. Qed.
Lemma D_a1bbc : decode_any W_a1bbc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bc0 : bv 32 := 0x00028a63.
Lemma F_a1bc0 : fetch_word AsanUbsan.M.loaded_segments (0xa1bc0 : word) = Some W_a1bc0.
Proof. vm_refl. Qed.
Lemma D_a1bc0 : decode_any W_a1bc0 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bc4 : bv 32 := 0x00170713.
Lemma F_a1bc4 : fetch_word AsanUbsan.M.loaded_segments (0xa1bc4 : word) = Some W_a1bc4.
Proof. vm_refl. Qed.
Lemma D_a1bc4 : decode_any W_a1bc4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bc8 : bv 32 := 0xfcf81ee3.
Lemma F_a1bc8 : fetch_word AsanUbsan.M.loaded_segments (0xa1bc8 : word) = Some W_a1bc8.
Proof. vm_refl. Qed.
Lemma D_a1bc8 : decode_any W_a1bc8 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bcc : bv 32 := 0x0080006f.
Lemma F_a1bcc : fetch_word AsanUbsan.M.loaded_segments (0xa1bcc : word) = Some W_a1bcc.
Proof. vm_refl. Qed.
Lemma D_a1bcc : decode_any W_a1bcc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bd0 : bv 32 := 0x00050693.
Lemma F_a1bd0 : fetch_word AsanUbsan.M.loaded_segments (0xa1bd0 : word) = Some W_a1bd0.
Proof. vm_refl. Qed.
Lemma D_a1bd0 : decode_any W_a1bd0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bd4 : bv 32 := 0x0036f793.
Lemma F_a1bd4 : fetch_word AsanUbsan.M.loaded_segments (0xa1bd4 : word) = Some W_a1bd4.
Proof. vm_refl. Qed.
Lemma D_a1bd4 : decode_any W_a1bd4 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bd8 : bv 32 := 0x0c078a63.
Lemma F_a1bd8 : fetch_word AsanUbsan.M.loaded_segments (0xa1bd8 : word) = Some W_a1bd8.
Proof. vm_refl. Qed.
Lemma D_a1bd8 : decode_any W_a1bd8 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bdc : bv 32 := 0x02000713.
Lemma F_a1bdc : fetch_word AsanUbsan.M.loaded_segments (0xa1bdc : word) = Some W_a1bdc.
Proof. vm_refl. Qed.
Lemma D_a1bdc : decode_any W_a1bdc = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1be0 : bv 32 := 0x02e67063.
Lemma F_a1be0 : fetch_word AsanUbsan.M.loaded_segments (0xa1be0 : word) = Some W_a1be0.
Proof. vm_refl. Qed.
Lemma D_a1be0 : decode_any W_a1be0 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1be4 : bv 32 := 0x01000713.
Lemma F_a1be4 : fetch_word AsanUbsan.M.loaded_segments (0xa1be4 : word) = Some W_a1be4.
Proof. vm_refl. Qed.
Lemma D_a1be4 : decode_any W_a1be4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1be8 : bv 32 := 0x24e67863.
Lemma F_a1be8 : fetch_word AsanUbsan.M.loaded_segments (0xa1be8 : word) = Some W_a1be8.
Proof. vm_refl. Qed.
Lemma D_a1be8 : decode_any W_a1be8 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bec : bv 32 := 0x00867713.
Lemma F_a1bec : fetch_word AsanUbsan.M.loaded_segments (0xa1bec : word) = Some W_a1bec.
Proof. vm_refl. Qed.
Lemma D_a1bec : decode_any W_a1bec = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bf0 : bv 32 := 0x2c071e63.
Lemma F_a1bf0 : fetch_word AsanUbsan.M.loaded_segments (0xa1bf0 : word) = Some W_a1bf0.
Proof. vm_refl. Qed.
Lemma D_a1bf0 : decode_any W_a1bf0 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bf4 : bv 32 := 0x00467713.
Lemma F_a1bf4 : fetch_word AsanUbsan.M.loaded_segments (0xa1bf4 : word) = Some W_a1bf4.
Proof. vm_refl. Qed.
Lemma D_a1bf4 : decode_any W_a1bf4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bf8 : bv 32 := 0x32071463.
Lemma F_a1bf8 : fetch_word AsanUbsan.M.loaded_segments (0xa1bf8 : word) = Some W_a1bf8.
Proof. vm_refl. Qed.
Lemma D_a1bf8 : decode_any W_a1bf8 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1bfc : bv 32 := 0x3500006f.
Lemma F_a1bfc : fetch_word AsanUbsan.M.loaded_segments (0xa1bfc : word) = Some W_a1bfc.
Proof. vm_refl. Qed.
Lemma D_a1bfc : decode_any W_a1bfc = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c00 : bv 32 := 0x0005a703.
Lemma F_a1c00 : fetch_word AsanUbsan.M.loaded_segments (0xa1c00 : word) = Some W_a1c00.
Proof. vm_refl. Qed.
Lemma D_a1c00 : decode_any W_a1c00 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c04 : bv 32 := 0x00300813.
Lemma F_a1c04 : fetch_word AsanUbsan.M.loaded_segments (0xa1c04 : word) = Some W_a1c04.
Proof. vm_refl. Qed.
Lemma D_a1c04 : decode_any W_a1c04 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c08 : bv 32 := 0x11078e63.
Lemma F_a1c08 : fetch_word AsanUbsan.M.loaded_segments (0xa1c08 : word) = Some W_a1c08.
Proof. vm_refl. Qed.
Lemma D_a1c08 : decode_any W_a1c08 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c0c : bv 32 := 0x00200813.
Lemma F_a1c0c : fetch_word AsanUbsan.M.loaded_segments (0xa1c0c : word) = Some W_a1c0c.
Proof. vm_refl. Qed.
Lemma D_a1c0c : decode_any W_a1c0c = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c10 : bv 32 := 0x19079c63.
Lemma F_a1c10 : fetch_word AsanUbsan.M.loaded_segments (0xa1c10 : word) = Some W_a1c10.
Proof. vm_refl. Qed.
Lemma D_a1c10 : decode_any W_a1c10 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c14 : bv 32 := 0x00875793.
Lemma F_a1c14 : fetch_word AsanUbsan.M.loaded_segments (0xa1c14 : word) = Some W_a1c14.
Proof. vm_refl. Qed.
Lemma D_a1c14 : decode_any W_a1c14 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c18 : bv 32 := 0xffe60613.
Lemma F_a1c18 : fetch_word AsanUbsan.M.loaded_segments (0xa1c18 : word) = Some W_a1c18.
Proof. vm_refl. Qed.
Lemma D_a1c18 : decode_any W_a1c18 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c1c : bv 32 := 0x00e68023.
Lemma F_a1c1c : fetch_word AsanUbsan.M.loaded_segments (0xa1c1c : word) = Some W_a1c1c.
Proof. vm_refl. Qed.
Lemma D_a1c1c : decode_any W_a1c1c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c20 : bv 32 := 0x00f680a3.
Lemma F_a1c20 : fetch_word AsanUbsan.M.loaded_segments (0xa1c20 : word) = Some W_a1c20.
Proof. vm_refl. Qed.
Lemma D_a1c20 : decode_any W_a1c20 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c24 : bv 32 := 0x00268693.
Lemma F_a1c24 : fetch_word AsanUbsan.M.loaded_segments (0xa1c24 : word) = Some W_a1c24.
Proof. vm_refl. Qed.
Lemma D_a1c24 : decode_any W_a1c24 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c28 : bv 32 := 0x01058593.
Lemma F_a1c28 : fetch_word AsanUbsan.M.loaded_segments (0xa1c28 : word) = Some W_a1c28.
Proof. vm_refl. Qed.
Lemma D_a1c28 : decode_any W_a1c28 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c2c : bv 32 := 0x01100793.
Lemma F_a1c2c : fetch_word AsanUbsan.M.loaded_segments (0xa1c2c : word) = Some W_a1c2c.
Proof. vm_refl. Qed.
Lemma D_a1c2c : decode_any W_a1c2c = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c30 : bv 32 := 0x0107581b.
Lemma F_a1c30 : fetch_word AsanUbsan.M.loaded_segments (0xa1c30 : word) = Some W_a1c30.
Proof. vm_refl. Qed.
Lemma D_a1c30 : decode_any W_a1c30 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c34 : bv 32 := 0xff45a883.
Lemma F_a1c34 : fetch_word AsanUbsan.M.loaded_segments (0xa1c34 : word) = Some W_a1c34.
Proof. vm_refl. Qed.
Lemma D_a1c34 : decode_any W_a1c34 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c38 : bv 32 := 0xff85a283.
Lemma F_a1c38 : fetch_word AsanUbsan.M.loaded_segments (0xa1c38 : word) = Some W_a1c38.
Proof. vm_refl. Qed.
Lemma D_a1c38 : decode_any W_a1c38 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c3c : bv 32 := 0xffc5a303.
Lemma F_a1c3c : fetch_word AsanUbsan.M.loaded_segments (0xa1c3c : word) = Some W_a1c3c.
Proof. vm_refl. Qed.
Lemma D_a1c3c : decode_any W_a1c3c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c40 : bv 32 := 0x0005a703.
Lemma F_a1c40 : fetch_word AsanUbsan.M.loaded_segments (0xa1c40 : word) = Some W_a1c40.
Proof. vm_refl. Qed.
Lemma D_a1c40 : decode_any W_a1c40 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c44 : bv 32 := 0x01089393.
Lemma F_a1c44 : fetch_word AsanUbsan.M.loaded_segments (0xa1c44 : word) = Some W_a1c44.
Proof. vm_refl. Qed.
Lemma D_a1c44 : decode_any W_a1c44 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c48 : bv 32 := 0x0108d89b.
Lemma F_a1c48 : fetch_word AsanUbsan.M.loaded_segments (0xa1c48 : word) = Some W_a1c48.
Proof. vm_refl. Qed.
Lemma D_a1c48 : decode_any W_a1c48 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c4c : bv 32 := 0x0103e833.
Lemma F_a1c4c : fetch_word AsanUbsan.M.loaded_segments (0xa1c4c : word) = Some W_a1c4c.
Proof. vm_refl. Qed.
Lemma D_a1c4c : decode_any W_a1c4c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c50 : bv 32 := 0x01029393.
Lemma F_a1c50 : fetch_word AsanUbsan.M.loaded_segments (0xa1c50 : word) = Some W_a1c50.
Proof. vm_refl. Qed.
Lemma D_a1c50 : decode_any W_a1c50 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c54 : bv 32 := 0x0102d29b.
Lemma F_a1c54 : fetch_word AsanUbsan.M.loaded_segments (0xa1c54 : word) = Some W_a1c54.
Proof. vm_refl. Qed.
Lemma D_a1c54 : decode_any W_a1c54 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c58 : bv 32 := 0x0113e8b3.
Lemma F_a1c58 : fetch_word AsanUbsan.M.loaded_segments (0xa1c58 : word) = Some W_a1c58.
Proof. vm_refl. Qed.
Lemma D_a1c58 : decode_any W_a1c58 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c5c : bv 32 := 0x01031393.
Lemma F_a1c5c : fetch_word AsanUbsan.M.loaded_segments (0xa1c5c : word) = Some W_a1c5c.
Proof. vm_refl. Qed.
Lemma D_a1c5c : decode_any W_a1c5c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c60 : bv 32 := 0x0103531b.
Lemma F_a1c60 : fetch_word AsanUbsan.M.loaded_segments (0xa1c60 : word) = Some W_a1c60.
Proof. vm_refl. Qed.
Lemma D_a1c60 : decode_any W_a1c60 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c64 : bv 32 := 0x0053e2b3.
Lemma F_a1c64 : fetch_word AsanUbsan.M.loaded_segments (0xa1c64 : word) = Some W_a1c64.
Proof. vm_refl. Qed.
Lemma D_a1c64 : decode_any W_a1c64 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c68 : bv 32 := 0x01071393.
Lemma F_a1c68 : fetch_word AsanUbsan.M.loaded_segments (0xa1c68 : word) = Some W_a1c68.
Proof. vm_refl. Qed.
Lemma D_a1c68 : decode_any W_a1c68 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c6c : bv 32 := 0x0063e333.
Lemma F_a1c6c : fetch_word AsanUbsan.M.loaded_segments (0xa1c6c : word) = Some W_a1c6c.
Proof. vm_refl. Qed.
Lemma D_a1c6c : decode_any W_a1c6c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c70 : bv 32 := 0xff060613.
Lemma F_a1c70 : fetch_word AsanUbsan.M.loaded_segments (0xa1c70 : word) = Some W_a1c70.
Proof. vm_refl. Qed.
Lemma D_a1c70 : decode_any W_a1c70 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c74 : bv 32 := 0x0106a023.
Lemma F_a1c74 : fetch_word AsanUbsan.M.loaded_segments (0xa1c74 : word) = Some W_a1c74.
Proof. vm_refl. Qed.
Lemma D_a1c74 : decode_any W_a1c74 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c78 : bv 32 := 0x0116a223.
Lemma F_a1c78 : fetch_word AsanUbsan.M.loaded_segments (0xa1c78 : word) = Some W_a1c78.
Proof. vm_refl. Qed.
Lemma D_a1c78 : decode_any W_a1c78 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c7c : bv 32 := 0x0056a423.
Lemma F_a1c7c : fetch_word AsanUbsan.M.loaded_segments (0xa1c7c : word) = Some W_a1c7c.
Proof. vm_refl. Qed.
Lemma D_a1c7c : decode_any W_a1c7c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c80 : bv 32 := 0x0066a623.
Lemma F_a1c80 : fetch_word AsanUbsan.M.loaded_segments (0xa1c80 : word) = Some W_a1c80.
Proof. vm_refl. Qed.
Lemma D_a1c80 : decode_any W_a1c80 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c84 : bv 32 := 0x01068693.
Lemma F_a1c84 : fetch_word AsanUbsan.M.loaded_segments (0xa1c84 : word) = Some W_a1c84.
Proof. vm_refl. Qed.
Lemma D_a1c84 : decode_any W_a1c84 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c88 : bv 32 := 0x01058593.
Lemma F_a1c88 : fetch_word AsanUbsan.M.loaded_segments (0xa1c88 : word) = Some W_a1c88.
Proof. vm_refl. Qed.
Lemma D_a1c88 : decode_any W_a1c88 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c8c : bv 32 := 0xfac7e2e3.
Lemma F_a1c8c : fetch_word AsanUbsan.M.loaded_segments (0xa1c8c : word) = Some W_a1c8c.
Proof. vm_refl. Qed.
Lemma D_a1c8c : decode_any W_a1c8c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c90 : bv 32 := 0xff258593.
Lemma F_a1c90 : fetch_word AsanUbsan.M.loaded_segments (0xa1c90 : word) = Some W_a1c90.
Proof. vm_refl. Qed.
Lemma D_a1c90 : decode_any W_a1c90 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c94 : bv 32 := 0x01000713.
Lemma F_a1c94 : fetch_word AsanUbsan.M.loaded_segments (0xa1c94 : word) = Some W_a1c94.
Proof. vm_refl. Qed.
Lemma D_a1c94 : decode_any W_a1c94 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c98 : bv 32 := 0xf4e66ae3.
Lemma F_a1c98 : fetch_word AsanUbsan.M.loaded_segments (0xa1c98 : word) = Some W_a1c98.
Proof. vm_refl. Qed.
Lemma D_a1c98 : decode_any W_a1c98 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1c9c : bv 32 := 0x19c0006f.
Lemma F_a1c9c : fetch_word AsanUbsan.M.loaded_segments (0xa1c9c : word) = Some W_a1c9c.
Proof. vm_refl. Qed.
Lemma D_a1c9c : decode_any W_a1c9c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ca0 : bv 32 := 0x00050693.
Lemma F_a1ca0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ca0 : word) = Some W_a1ca0.
Proof. vm_refl. Qed.
Lemma D_a1ca0 : decode_any W_a1ca0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ca4 : bv 32 := 0x00357793.
Lemma F_a1ca4 : fetch_word AsanUbsan.M.loaded_segments (0xa1ca4 : word) = Some W_a1ca4.
Proof. vm_refl. Qed.
Lemma D_a1ca4 : decode_any W_a1ca4 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ca8 : bv 32 := 0xf2079ae3.
Lemma F_a1ca8 : fetch_word AsanUbsan.M.loaded_segments (0xa1ca8 : word) = Some W_a1ca8.
Proof. vm_refl. Qed.
Lemma D_a1ca8 : decode_any W_a1ca8 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cac : bv 32 := 0x01000713.
Lemma F_a1cac : fetch_word AsanUbsan.M.loaded_segments (0xa1cac : word) = Some W_a1cac.
Proof. vm_refl. Qed.
Lemma D_a1cac : decode_any W_a1cac = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cb0 : bv 32 := 0x02e66c63.
Lemma F_a1cb0 : fetch_word AsanUbsan.M.loaded_segments (0xa1cb0 : word) = Some W_a1cb0.
Proof. vm_refl. Qed.
Lemma D_a1cb0 : decode_any W_a1cb0 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cb4 : bv 32 := 0x00f00713.
Lemma F_a1cb4 : fetch_word AsanUbsan.M.loaded_segments (0xa1cb4 : word) = Some W_a1cb4.
Proof. vm_refl. Qed.
Lemma D_a1cb4 : decode_any W_a1cb4 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cb8 : bv 32 := 0x0005a783.
Lemma F_a1cb8 : fetch_word AsanUbsan.M.loaded_segments (0xa1cb8 : word) = Some W_a1cb8.
Proof. vm_refl. Qed.
Lemma D_a1cb8 : decode_any W_a1cb8 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cbc : bv 32 := 0x0045a803.
Lemma F_a1cbc : fetch_word AsanUbsan.M.loaded_segments (0xa1cbc : word) = Some W_a1cbc.
Proof. vm_refl. Qed.
Lemma D_a1cbc : decode_any W_a1cbc = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cc0 : bv 32 := 0x0085a883.
Lemma F_a1cc0 : fetch_word AsanUbsan.M.loaded_segments (0xa1cc0 : word) = Some W_a1cc0.
Proof. vm_refl. Qed.
Lemma D_a1cc0 : decode_any W_a1cc0 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cc4 : bv 32 := 0x00c5a283.
Lemma F_a1cc4 : fetch_word AsanUbsan.M.loaded_segments (0xa1cc4 : word) = Some W_a1cc4.
Proof. vm_refl. Qed.
Lemma D_a1cc4 : decode_any W_a1cc4 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cc8 : bv 32 := 0x01058593.
Lemma F_a1cc8 : fetch_word AsanUbsan.M.loaded_segments (0xa1cc8 : word) = Some W_a1cc8.
Proof. vm_refl. Qed.
Lemma D_a1cc8 : decode_any W_a1cc8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ccc : bv 32 := 0xff060613.
Lemma F_a1ccc : fetch_word AsanUbsan.M.loaded_segments (0xa1ccc : word) = Some W_a1ccc.
Proof. vm_refl. Qed.
Lemma D_a1ccc : decode_any W_a1ccc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cd0 : bv 32 := 0x00f6a023.
Lemma F_a1cd0 : fetch_word AsanUbsan.M.loaded_segments (0xa1cd0 : word) = Some W_a1cd0.
Proof. vm_refl. Qed.
Lemma D_a1cd0 : decode_any W_a1cd0 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cd4 : bv 32 := 0x0106a223.
Lemma F_a1cd4 : fetch_word AsanUbsan.M.loaded_segments (0xa1cd4 : word) = Some W_a1cd4.
Proof. vm_refl. Qed.
Lemma D_a1cd4 : decode_any W_a1cd4 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cd8 : bv 32 := 0x0116a423.
Lemma F_a1cd8 : fetch_word AsanUbsan.M.loaded_segments (0xa1cd8 : word) = Some W_a1cd8.
Proof. vm_refl. Qed.
Lemma D_a1cd8 : decode_any W_a1cd8 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cdc : bv 32 := 0x0056a623.
Lemma F_a1cdc : fetch_word AsanUbsan.M.loaded_segments (0xa1cdc : word) = Some W_a1cdc.
Proof. vm_refl. Qed.
Lemma D_a1cdc : decode_any W_a1cdc = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ce0 : bv 32 := 0x01068693.
Lemma F_a1ce0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ce0 : word) = Some W_a1ce0.
Proof. vm_refl. Qed.
Lemma D_a1ce0 : decode_any W_a1ce0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ce4 : bv 32 := 0xfcc76ae3.
Lemma F_a1ce4 : fetch_word AsanUbsan.M.loaded_segments (0xa1ce4 : word) = Some W_a1ce4.
Proof. vm_refl. Qed.
Lemma D_a1ce4 : decode_any W_a1ce4 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ce8 : bv 32 := 0x00800713.
Lemma F_a1ce8 : fetch_word AsanUbsan.M.loaded_segments (0xa1ce8 : word) = Some W_a1ce8.
Proof. vm_refl. Qed.
Lemma D_a1ce8 : decode_any W_a1ce8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cec : bv 32 := 0x00e66e63.
Lemma F_a1cec : fetch_word AsanUbsan.M.loaded_segments (0xa1cec : word) = Some W_a1cec.
Proof. vm_refl. Qed.
Lemma D_a1cec : decode_any W_a1cec = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cf0 : bv 32 := 0x0005a703.
Lemma F_a1cf0 : fetch_word AsanUbsan.M.loaded_segments (0xa1cf0 : word) = Some W_a1cf0.
Proof. vm_refl. Qed.
Lemma D_a1cf0 : decode_any W_a1cf0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cf4 : bv 32 := 0x0045a783.
Lemma F_a1cf4 : fetch_word AsanUbsan.M.loaded_segments (0xa1cf4 : word) = Some W_a1cf4.
Proof. vm_refl. Qed.
Lemma D_a1cf4 : decode_any W_a1cf4 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cf8 : bv 32 := 0x00e6a023.
Lemma F_a1cf8 : fetch_word AsanUbsan.M.loaded_segments (0xa1cf8 : word) = Some W_a1cf8.
Proof. vm_refl. Qed.
Lemma D_a1cf8 : decode_any W_a1cf8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1cfc : bv 32 := 0x00f6a223.
Lemma F_a1cfc : fetch_word AsanUbsan.M.loaded_segments (0xa1cfc : word) = Some W_a1cfc.
Proof. vm_refl. Qed.
Lemma D_a1cfc : decode_any W_a1cfc = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d00 : bv 32 := 0x00868693.
Lemma F_a1d00 : fetch_word AsanUbsan.M.loaded_segments (0xa1d00 : word) = Some W_a1d00.
Proof. vm_refl. Qed.
Lemma D_a1d00 : decode_any W_a1d00 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d04 : bv 32 := 0x00858593.
Lemma F_a1d04 : fetch_word AsanUbsan.M.loaded_segments (0xa1d04 : word) = Some W_a1d04.
Proof. vm_refl. Qed.
Lemma D_a1d04 : decode_any W_a1d04 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d08 : bv 32 := 0x00467713.
Lemma F_a1d08 : fetch_word AsanUbsan.M.loaded_segments (0xa1d08 : word) = Some W_a1d08.
Proof. vm_refl. Qed.
Lemma D_a1d08 : decode_any W_a1d08 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d0c : bv 32 := 0x24070063.
Lemma F_a1d0c : fetch_word AsanUbsan.M.loaded_segments (0xa1d0c : word) = Some W_a1d0c.
Proof. vm_refl. Qed.
Lemma D_a1d0c : decode_any W_a1d0c = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d10 : bv 32 := 0x0005a703.
Lemma F_a1d10 : fetch_word AsanUbsan.M.loaded_segments (0xa1d10 : word) = Some W_a1d10.
Proof. vm_refl. Qed.
Lemma D_a1d10 : decode_any W_a1d10 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d14 : bv 32 := 0x00458593.
Lemma F_a1d14 : fetch_word AsanUbsan.M.loaded_segments (0xa1d14 : word) = Some W_a1d14.
Proof. vm_refl. Qed.
Lemma D_a1d14 : decode_any W_a1d14 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d18 : bv 32 := 0x00e6a023.
Lemma F_a1d18 : fetch_word AsanUbsan.M.loaded_segments (0xa1d18 : word) = Some W_a1d18.
Proof. vm_refl. Qed.
Lemma D_a1d18 : decode_any W_a1d18 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d1c : bv 32 := 0x00468693.
Lemma F_a1d1c : fetch_word AsanUbsan.M.loaded_segments (0xa1d1c : word) = Some W_a1d1c.
Proof. vm_refl. Qed.
Lemma D_a1d1c : decode_any W_a1d1c = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d20 : bv 32 := 0x22c0006f.
Lemma F_a1d20 : fetch_word AsanUbsan.M.loaded_segments (0xa1d20 : word) = Some W_a1d20.
Proof. vm_refl. Qed.
Lemma D_a1d20 : decode_any W_a1d20 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d24 : bv 32 := 0x00e68023.
Lemma F_a1d24 : fetch_word AsanUbsan.M.loaded_segments (0xa1d24 : word) = Some W_a1d24.
Proof. vm_refl. Qed.
Lemma D_a1d24 : decode_any W_a1d24 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d28 : bv 32 := 0x00168693.
Lemma F_a1d28 : fetch_word AsanUbsan.M.loaded_segments (0xa1d28 : word) = Some W_a1d28.
Proof. vm_refl. Qed.
Lemma D_a1d28 : decode_any W_a1d28 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d2c : bv 32 := 0xfff60613.
Lemma F_a1d2c : fetch_word AsanUbsan.M.loaded_segments (0xa1d2c : word) = Some W_a1d2c.
Proof. vm_refl. Qed.
Lemma D_a1d2c : decode_any W_a1d2c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d30 : bv 32 := 0x01058593.
Lemma F_a1d30 : fetch_word AsanUbsan.M.loaded_segments (0xa1d30 : word) = Some W_a1d30.
Proof. vm_refl. Qed.
Lemma D_a1d30 : decode_any W_a1d30 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d34 : bv 32 := 0x01200793.
Lemma F_a1d34 : fetch_word AsanUbsan.M.loaded_segments (0xa1d34 : word) = Some W_a1d34.
Proof. vm_refl. Qed.
Lemma D_a1d34 : decode_any W_a1d34 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d38 : bv 32 := 0x0087581b.
Lemma F_a1d38 : fetch_word AsanUbsan.M.loaded_segments (0xa1d38 : word) = Some W_a1d38.
Proof. vm_refl. Qed.
Lemma D_a1d38 : decode_any W_a1d38 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d3c : bv 32 := 0xff45a883.
Lemma F_a1d3c : fetch_word AsanUbsan.M.loaded_segments (0xa1d3c : word) = Some W_a1d3c.
Proof. vm_refl. Qed.
Lemma D_a1d3c : decode_any W_a1d3c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d40 : bv 32 := 0xff85a283.
Lemma F_a1d40 : fetch_word AsanUbsan.M.loaded_segments (0xa1d40 : word) = Some W_a1d40.
Proof. vm_refl. Qed.
Lemma D_a1d40 : decode_any W_a1d40 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d44 : bv 32 := 0xffc5a303.
Lemma F_a1d44 : fetch_word AsanUbsan.M.loaded_segments (0xa1d44 : word) = Some W_a1d44.
Proof. vm_refl. Qed.
Lemma D_a1d44 : decode_any W_a1d44 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d48 : bv 32 := 0x0005a703.
Lemma F_a1d48 : fetch_word AsanUbsan.M.loaded_segments (0xa1d48 : word) = Some W_a1d48.
Proof. vm_refl. Qed.
Lemma D_a1d48 : decode_any W_a1d48 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d4c : bv 32 := 0x01889393.
Lemma F_a1d4c : fetch_word AsanUbsan.M.loaded_segments (0xa1d4c : word) = Some W_a1d4c.
Proof. vm_refl. Qed.
Lemma D_a1d4c : decode_any W_a1d4c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d50 : bv 32 := 0x0088d89b.
Lemma F_a1d50 : fetch_word AsanUbsan.M.loaded_segments (0xa1d50 : word) = Some W_a1d50.
Proof. vm_refl. Qed.
Lemma D_a1d50 : decode_any W_a1d50 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d54 : bv 32 := 0x0103e833.
Lemma F_a1d54 : fetch_word AsanUbsan.M.loaded_segments (0xa1d54 : word) = Some W_a1d54.
Proof. vm_refl. Qed.
Lemma D_a1d54 : decode_any W_a1d54 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d58 : bv 32 := 0x01829393.
Lemma F_a1d58 : fetch_word AsanUbsan.M.loaded_segments (0xa1d58 : word) = Some W_a1d58.
Proof. vm_refl. Qed.
Lemma D_a1d58 : decode_any W_a1d58 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d5c : bv 32 := 0x0082d29b.
Lemma F_a1d5c : fetch_word AsanUbsan.M.loaded_segments (0xa1d5c : word) = Some W_a1d5c.
Proof. vm_refl. Qed.
Lemma D_a1d5c : decode_any W_a1d5c = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d60 : bv 32 := 0x0113e8b3.
Lemma F_a1d60 : fetch_word AsanUbsan.M.loaded_segments (0xa1d60 : word) = Some W_a1d60.
Proof. vm_refl. Qed.
Lemma D_a1d60 : decode_any W_a1d60 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d64 : bv 32 := 0x01831393.
Lemma F_a1d64 : fetch_word AsanUbsan.M.loaded_segments (0xa1d64 : word) = Some W_a1d64.
Proof. vm_refl. Qed.
Lemma D_a1d64 : decode_any W_a1d64 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d68 : bv 32 := 0x0083531b.
Lemma F_a1d68 : fetch_word AsanUbsan.M.loaded_segments (0xa1d68 : word) = Some W_a1d68.
Proof. vm_refl. Qed.
Lemma D_a1d68 : decode_any W_a1d68 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d6c : bv 32 := 0x0053e2b3.
Lemma F_a1d6c : fetch_word AsanUbsan.M.loaded_segments (0xa1d6c : word) = Some W_a1d6c.
Proof. vm_refl. Qed.
Lemma D_a1d6c : decode_any W_a1d6c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d70 : bv 32 := 0x01871393.
Lemma F_a1d70 : fetch_word AsanUbsan.M.loaded_segments (0xa1d70 : word) = Some W_a1d70.
Proof. vm_refl. Qed.
Lemma D_a1d70 : decode_any W_a1d70 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d74 : bv 32 := 0x0063e333.
Lemma F_a1d74 : fetch_word AsanUbsan.M.loaded_segments (0xa1d74 : word) = Some W_a1d74.
Proof. vm_refl. Qed.
Lemma D_a1d74 : decode_any W_a1d74 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d78 : bv 32 := 0xff060613.
Lemma F_a1d78 : fetch_word AsanUbsan.M.loaded_segments (0xa1d78 : word) = Some W_a1d78.
Proof. vm_refl. Qed.
Lemma D_a1d78 : decode_any W_a1d78 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d7c : bv 32 := 0x0106a023.
Lemma F_a1d7c : fetch_word AsanUbsan.M.loaded_segments (0xa1d7c : word) = Some W_a1d7c.
Proof. vm_refl. Qed.
Lemma D_a1d7c : decode_any W_a1d7c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d80 : bv 32 := 0x0116a223.
Lemma F_a1d80 : fetch_word AsanUbsan.M.loaded_segments (0xa1d80 : word) = Some W_a1d80.
Proof. vm_refl. Qed.
Lemma D_a1d80 : decode_any W_a1d80 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d84 : bv 32 := 0x0056a423.
Lemma F_a1d84 : fetch_word AsanUbsan.M.loaded_segments (0xa1d84 : word) = Some W_a1d84.
Proof. vm_refl. Qed.
Lemma D_a1d84 : decode_any W_a1d84 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d88 : bv 32 := 0x0066a623.
Lemma F_a1d88 : fetch_word AsanUbsan.M.loaded_segments (0xa1d88 : word) = Some W_a1d88.
Proof. vm_refl. Qed.
Lemma D_a1d88 : decode_any W_a1d88 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d8c : bv 32 := 0x01068693.
Lemma F_a1d8c : fetch_word AsanUbsan.M.loaded_segments (0xa1d8c : word) = Some W_a1d8c.
Proof. vm_refl. Qed.
Lemma D_a1d8c : decode_any W_a1d8c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d90 : bv 32 := 0x01058593.
Lemma F_a1d90 : fetch_word AsanUbsan.M.loaded_segments (0xa1d90 : word) = Some W_a1d90.
Proof. vm_refl. Qed.
Lemma D_a1d90 : decode_any W_a1d90 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d94 : bv 32 := 0xfac7e2e3.
Lemma F_a1d94 : fetch_word AsanUbsan.M.loaded_segments (0xa1d94 : word) = Some W_a1d94.
Proof. vm_refl. Qed.
Lemma D_a1d94 : decode_any W_a1d94 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d98 : bv 32 := 0xff158593.
Lemma F_a1d98 : fetch_word AsanUbsan.M.loaded_segments (0xa1d98 : word) = Some W_a1d98.
Proof. vm_refl. Qed.
Lemma D_a1d98 : decode_any W_a1d98 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1d9c : bv 32 := 0x01000713.
Lemma F_a1d9c : fetch_word AsanUbsan.M.loaded_segments (0xa1d9c : word) = Some W_a1d9c.
Proof. vm_refl. Qed.
Lemma D_a1d9c : decode_any W_a1d9c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1da0 : bv 32 := 0xe4e666e3.
Lemma F_a1da0 : fetch_word AsanUbsan.M.loaded_segments (0xa1da0 : word) = Some W_a1da0.
Proof. vm_refl. Qed.
Lemma D_a1da0 : decode_any W_a1da0 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1da4 : bv 32 := 0x0940006f.
Lemma F_a1da4 : fetch_word AsanUbsan.M.loaded_segments (0xa1da4 : word) = Some W_a1da4.
Proof. vm_refl. Qed.
Lemma D_a1da4 : decode_any W_a1da4 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1da8 : bv 32 := 0x00875793.
Lemma F_a1da8 : fetch_word AsanUbsan.M.loaded_segments (0xa1da8 : word) = Some W_a1da8.
Proof. vm_refl. Qed.
Lemma D_a1da8 : decode_any W_a1da8 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1dac : bv 32 := 0x01075813.
Lemma F_a1dac : fetch_word AsanUbsan.M.loaded_segments (0xa1dac : word) = Some W_a1dac.
Proof. vm_refl. Qed.
Lemma D_a1dac : decode_any W_a1dac = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1db0 : bv 32 := 0xffd60613.
Lemma F_a1db0 : fetch_word AsanUbsan.M.loaded_segments (0xa1db0 : word) = Some W_a1db0.
Proof. vm_refl. Qed.
Lemma D_a1db0 : decode_any W_a1db0 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1db4 : bv 32 := 0x00e68023.
Lemma F_a1db4 : fetch_word AsanUbsan.M.loaded_segments (0xa1db4 : word) = Some W_a1db4.
Proof. vm_refl. Qed.
Lemma D_a1db4 : decode_any W_a1db4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1db8 : bv 32 := 0x00f680a3.
Lemma F_a1db8 : fetch_word AsanUbsan.M.loaded_segments (0xa1db8 : word) = Some W_a1db8.
Proof. vm_refl. Qed.
Lemma D_a1db8 : decode_any W_a1db8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1dbc : bv 32 := 0x01068123.
Lemma F_a1dbc : fetch_word AsanUbsan.M.loaded_segments (0xa1dbc : word) = Some W_a1dbc.
Proof. vm_refl. Qed.
Lemma D_a1dbc : decode_any W_a1dbc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1dc0 : bv 32 := 0x00368693.
Lemma F_a1dc0 : fetch_word AsanUbsan.M.loaded_segments (0xa1dc0 : word) = Some W_a1dc0.
Proof. vm_refl. Qed.
Lemma D_a1dc0 : decode_any W_a1dc0 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1dc4 : bv 32 := 0x01058593.
Lemma F_a1dc4 : fetch_word AsanUbsan.M.loaded_segments (0xa1dc4 : word) = Some W_a1dc4.
Proof. vm_refl. Qed.
Lemma D_a1dc4 : decode_any W_a1dc4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1dc8 : bv 32 := 0x01000793.
Lemma F_a1dc8 : fetch_word AsanUbsan.M.loaded_segments (0xa1dc8 : word) = Some W_a1dc8.
Proof. vm_refl. Qed.
Lemma D_a1dc8 : decode_any W_a1dc8 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1dcc : bv 32 := 0x0187581b.
Lemma F_a1dcc : fetch_word AsanUbsan.M.loaded_segments (0xa1dcc : word) = Some W_a1dcc.
Proof. vm_refl. Qed.
Lemma D_a1dcc : decode_any W_a1dcc = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1dd0 : bv 32 := 0xff45a883.
Lemma F_a1dd0 : fetch_word AsanUbsan.M.loaded_segments (0xa1dd0 : word) = Some W_a1dd0.
Proof. vm_refl. Qed.
Lemma D_a1dd0 : decode_any W_a1dd0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1dd4 : bv 32 := 0xff85a283.
Lemma F_a1dd4 : fetch_word AsanUbsan.M.loaded_segments (0xa1dd4 : word) = Some W_a1dd4.
Proof. vm_refl. Qed.
Lemma D_a1dd4 : decode_any W_a1dd4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1dd8 : bv 32 := 0xffc5a303.
Lemma F_a1dd8 : fetch_word AsanUbsan.M.loaded_segments (0xa1dd8 : word) = Some W_a1dd8.
Proof. vm_refl. Qed.
Lemma D_a1dd8 : decode_any W_a1dd8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ddc : bv 32 := 0x0005a703.
Lemma F_a1ddc : fetch_word AsanUbsan.M.loaded_segments (0xa1ddc : word) = Some W_a1ddc.
Proof. vm_refl. Qed.
Lemma D_a1ddc : decode_any W_a1ddc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1de0 : bv 32 := 0x00889393.
Lemma F_a1de0 : fetch_word AsanUbsan.M.loaded_segments (0xa1de0 : word) = Some W_a1de0.
Proof. vm_refl. Qed.
Lemma D_a1de0 : decode_any W_a1de0 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1de4 : bv 32 := 0x0188d89b.
Lemma F_a1de4 : fetch_word AsanUbsan.M.loaded_segments (0xa1de4 : word) = Some W_a1de4.
Proof. vm_refl. Qed.
Lemma D_a1de4 : decode_any W_a1de4 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1de8 : bv 32 := 0x0103e833.
Lemma F_a1de8 : fetch_word AsanUbsan.M.loaded_segments (0xa1de8 : word) = Some W_a1de8.
Proof. vm_refl. Qed.
Lemma D_a1de8 : decode_any W_a1de8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1dec : bv 32 := 0x00829393.
Lemma F_a1dec : fetch_word AsanUbsan.M.loaded_segments (0xa1dec : word) = Some W_a1dec.
Proof. vm_refl. Qed.
Lemma D_a1dec : decode_any W_a1dec = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1df0 : bv 32 := 0x0182d29b.
Lemma F_a1df0 : fetch_word AsanUbsan.M.loaded_segments (0xa1df0 : word) = Some W_a1df0.
Proof. vm_refl. Qed.
Lemma D_a1df0 : decode_any W_a1df0 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1df4 : bv 32 := 0x0113e8b3.
Lemma F_a1df4 : fetch_word AsanUbsan.M.loaded_segments (0xa1df4 : word) = Some W_a1df4.
Proof. vm_refl. Qed.
Lemma D_a1df4 : decode_any W_a1df4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1df8 : bv 32 := 0x00831393.
Lemma F_a1df8 : fetch_word AsanUbsan.M.loaded_segments (0xa1df8 : word) = Some W_a1df8.
Proof. vm_refl. Qed.
Lemma D_a1df8 : decode_any W_a1df8 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1dfc : bv 32 := 0x0183531b.
Lemma F_a1dfc : fetch_word AsanUbsan.M.loaded_segments (0xa1dfc : word) = Some W_a1dfc.
Proof. vm_refl. Qed.
Lemma D_a1dfc : decode_any W_a1dfc = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e00 : bv 32 := 0x0053e2b3.
Lemma F_a1e00 : fetch_word AsanUbsan.M.loaded_segments (0xa1e00 : word) = Some W_a1e00.
Proof. vm_refl. Qed.
Lemma D_a1e00 : decode_any W_a1e00 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e04 : bv 32 := 0x00871393.
Lemma F_a1e04 : fetch_word AsanUbsan.M.loaded_segments (0xa1e04 : word) = Some W_a1e04.
Proof. vm_refl. Qed.
Lemma D_a1e04 : decode_any W_a1e04 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e08 : bv 32 := 0x0063e333.
Lemma F_a1e08 : fetch_word AsanUbsan.M.loaded_segments (0xa1e08 : word) = Some W_a1e08.
Proof. vm_refl. Qed.
Lemma D_a1e08 : decode_any W_a1e08 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e0c : bv 32 := 0xff060613.
Lemma F_a1e0c : fetch_word AsanUbsan.M.loaded_segments (0xa1e0c : word) = Some W_a1e0c.
Proof. vm_refl. Qed.
Lemma D_a1e0c : decode_any W_a1e0c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e10 : bv 32 := 0x0106a023.
Lemma F_a1e10 : fetch_word AsanUbsan.M.loaded_segments (0xa1e10 : word) = Some W_a1e10.
Proof. vm_refl. Qed.
Lemma D_a1e10 : decode_any W_a1e10 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e14 : bv 32 := 0x0116a223.
Lemma F_a1e14 : fetch_word AsanUbsan.M.loaded_segments (0xa1e14 : word) = Some W_a1e14.
Proof. vm_refl. Qed.
Lemma D_a1e14 : decode_any W_a1e14 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e18 : bv 32 := 0x0056a423.
Lemma F_a1e18 : fetch_word AsanUbsan.M.loaded_segments (0xa1e18 : word) = Some W_a1e18.
Proof. vm_refl. Qed.
Lemma D_a1e18 : decode_any W_a1e18 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e1c : bv 32 := 0x0066a623.
Lemma F_a1e1c : fetch_word AsanUbsan.M.loaded_segments (0xa1e1c : word) = Some W_a1e1c.
Proof. vm_refl. Qed.
Lemma D_a1e1c : decode_any W_a1e1c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e20 : bv 32 := 0x01068693.
Lemma F_a1e20 : fetch_word AsanUbsan.M.loaded_segments (0xa1e20 : word) = Some W_a1e20.
Proof. vm_refl. Qed.
Lemma D_a1e20 : decode_any W_a1e20 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e24 : bv 32 := 0x01058593.
Lemma F_a1e24 : fetch_word AsanUbsan.M.loaded_segments (0xa1e24 : word) = Some W_a1e24.
Proof. vm_refl. Qed.
Lemma D_a1e24 : decode_any W_a1e24 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e28 : bv 32 := 0xfac7e2e3.
Lemma F_a1e28 : fetch_word AsanUbsan.M.loaded_segments (0xa1e28 : word) = Some W_a1e28.
Proof. vm_refl. Qed.
Lemma D_a1e28 : decode_any W_a1e28 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e2c : bv 32 := 0xff358593.
Lemma F_a1e2c : fetch_word AsanUbsan.M.loaded_segments (0xa1e2c : word) = Some W_a1e2c.
Proof. vm_refl. Qed.
Lemma D_a1e2c : decode_any W_a1e2c = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e30 : bv 32 := 0x01000713.
Lemma F_a1e30 : fetch_word AsanUbsan.M.loaded_segments (0xa1e30 : word) = Some W_a1e30.
Proof. vm_refl. Qed.
Lemma D_a1e30 : decode_any W_a1e30 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e34 : bv 32 := 0xdae66ce3.
Lemma F_a1e34 : fetch_word AsanUbsan.M.loaded_segments (0xa1e34 : word) = Some W_a1e34.
Proof. vm_refl. Qed.
Lemma D_a1e34 : decode_any W_a1e34 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e38 : bv 32 := 0x0005c703.
Lemma F_a1e38 : fetch_word AsanUbsan.M.loaded_segments (0xa1e38 : word) = Some W_a1e38.
Proof. vm_refl. Qed.
Lemma D_a1e38 : decode_any W_a1e38 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e3c : bv 32 := 0x0015c783.
Lemma F_a1e3c : fetch_word AsanUbsan.M.loaded_segments (0xa1e3c : word) = Some W_a1e3c.
Proof. vm_refl. Qed.
Lemma D_a1e3c : decode_any W_a1e3c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e40 : bv 32 := 0x0025c803.
Lemma F_a1e40 : fetch_word AsanUbsan.M.loaded_segments (0xa1e40 : word) = Some W_a1e40.
Proof. vm_refl. Qed.
Lemma D_a1e40 : decode_any W_a1e40 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e44 : bv 32 := 0x0035c883.
Lemma F_a1e44 : fetch_word AsanUbsan.M.loaded_segments (0xa1e44 : word) = Some W_a1e44.
Proof. vm_refl. Qed.
Lemma D_a1e44 : decode_any W_a1e44 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e48 : bv 32 := 0x0045c283.
Lemma F_a1e48 : fetch_word AsanUbsan.M.loaded_segments (0xa1e48 : word) = Some W_a1e48.
Proof. vm_refl. Qed.
Lemma D_a1e48 : decode_any W_a1e48 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e4c : bv 32 := 0x0055c303.
Lemma F_a1e4c : fetch_word AsanUbsan.M.loaded_segments (0xa1e4c : word) = Some W_a1e4c.
Proof. vm_refl. Qed.
Lemma D_a1e4c : decode_any W_a1e4c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e50 : bv 32 := 0x0065c383.
Lemma F_a1e50 : fetch_word AsanUbsan.M.loaded_segments (0xa1e50 : word) = Some W_a1e50.
Proof. vm_refl. Qed.
Lemma D_a1e50 : decode_any W_a1e50 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e54 : bv 32 := 0x0075ce03.
Lemma F_a1e54 : fetch_word AsanUbsan.M.loaded_segments (0xa1e54 : word) = Some W_a1e54.
Proof. vm_refl. Qed.
Lemma D_a1e54 : decode_any W_a1e54 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e58 : bv 32 := 0x00e68023.
Lemma F_a1e58 : fetch_word AsanUbsan.M.loaded_segments (0xa1e58 : word) = Some W_a1e58.
Proof. vm_refl. Qed.
Lemma D_a1e58 : decode_any W_a1e58 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e5c : bv 32 := 0x00f680a3.
Lemma F_a1e5c : fetch_word AsanUbsan.M.loaded_segments (0xa1e5c : word) = Some W_a1e5c.
Proof. vm_refl. Qed.
Lemma D_a1e5c : decode_any W_a1e5c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e60 : bv 32 := 0x01068123.
Lemma F_a1e60 : fetch_word AsanUbsan.M.loaded_segments (0xa1e60 : word) = Some W_a1e60.
Proof. vm_refl. Qed.
Lemma D_a1e60 : decode_any W_a1e60 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e64 : bv 32 := 0x011681a3.
Lemma F_a1e64 : fetch_word AsanUbsan.M.loaded_segments (0xa1e64 : word) = Some W_a1e64.
Proof. vm_refl. Qed.
Lemma D_a1e64 : decode_any W_a1e64 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e68 : bv 32 := 0x0085c703.
Lemma F_a1e68 : fetch_word AsanUbsan.M.loaded_segments (0xa1e68 : word) = Some W_a1e68.
Proof. vm_refl. Qed.
Lemma D_a1e68 : decode_any W_a1e68 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e6c : bv 32 := 0x0095c783.
Lemma F_a1e6c : fetch_word AsanUbsan.M.loaded_segments (0xa1e6c : word) = Some W_a1e6c.
Proof. vm_refl. Qed.
Lemma D_a1e6c : decode_any W_a1e6c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e70 : bv 32 := 0x00a5c803.
Lemma F_a1e70 : fetch_word AsanUbsan.M.loaded_segments (0xa1e70 : word) = Some W_a1e70.
Proof. vm_refl. Qed.
Lemma D_a1e70 : decode_any W_a1e70 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e74 : bv 32 := 0x00b5c883.
Lemma F_a1e74 : fetch_word AsanUbsan.M.loaded_segments (0xa1e74 : word) = Some W_a1e74.
Proof. vm_refl. Qed.
Lemma D_a1e74 : decode_any W_a1e74 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e78 : bv 32 := 0x00568223.
Lemma F_a1e78 : fetch_word AsanUbsan.M.loaded_segments (0xa1e78 : word) = Some W_a1e78.
Proof. vm_refl. Qed.
Lemma D_a1e78 : decode_any W_a1e78 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e7c : bv 32 := 0x006682a3.
Lemma F_a1e7c : fetch_word AsanUbsan.M.loaded_segments (0xa1e7c : word) = Some W_a1e7c.
Proof. vm_refl. Qed.
Lemma D_a1e7c : decode_any W_a1e7c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e80 : bv 32 := 0x00768323.
Lemma F_a1e80 : fetch_word AsanUbsan.M.loaded_segments (0xa1e80 : word) = Some W_a1e80.
Proof. vm_refl. Qed.
Lemma D_a1e80 : decode_any W_a1e80 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e84 : bv 32 := 0x01c683a3.
Lemma F_a1e84 : fetch_word AsanUbsan.M.loaded_segments (0xa1e84 : word) = Some W_a1e84.
Proof. vm_refl. Qed.
Lemma D_a1e84 : decode_any W_a1e84 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e88 : bv 32 := 0x00c5c283.
Lemma F_a1e88 : fetch_word AsanUbsan.M.loaded_segments (0xa1e88 : word) = Some W_a1e88.
Proof. vm_refl. Qed.
Lemma D_a1e88 : decode_any W_a1e88 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e8c : bv 32 := 0x00d5c303.
Lemma F_a1e8c : fetch_word AsanUbsan.M.loaded_segments (0xa1e8c : word) = Some W_a1e8c.
Proof. vm_refl. Qed.
Lemma D_a1e8c : decode_any W_a1e8c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e90 : bv 32 := 0x00e5c383.
Lemma F_a1e90 : fetch_word AsanUbsan.M.loaded_segments (0xa1e90 : word) = Some W_a1e90.
Proof. vm_refl. Qed.
Lemma D_a1e90 : decode_any W_a1e90 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e94 : bv 32 := 0x00f5ce03.
Lemma F_a1e94 : fetch_word AsanUbsan.M.loaded_segments (0xa1e94 : word) = Some W_a1e94.
Proof. vm_refl. Qed.
Lemma D_a1e94 : decode_any W_a1e94 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e98 : bv 32 := 0x01058593.
Lemma F_a1e98 : fetch_word AsanUbsan.M.loaded_segments (0xa1e98 : word) = Some W_a1e98.
Proof. vm_refl. Qed.
Lemma D_a1e98 : decode_any W_a1e98 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1e9c : bv 32 := 0x00e68423.
Lemma F_a1e9c : fetch_word AsanUbsan.M.loaded_segments (0xa1e9c : word) = Some W_a1e9c.
Proof. vm_refl. Qed.
Lemma D_a1e9c : decode_any W_a1e9c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ea0 : bv 32 := 0x00f684a3.
Lemma F_a1ea0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ea0 : word) = Some W_a1ea0.
Proof. vm_refl. Qed.
Lemma D_a1ea0 : decode_any W_a1ea0 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ea4 : bv 32 := 0x01068523.
Lemma F_a1ea4 : fetch_word AsanUbsan.M.loaded_segments (0xa1ea4 : word) = Some W_a1ea4.
Proof. vm_refl. Qed.
Lemma D_a1ea4 : decode_any W_a1ea4 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ea8 : bv 32 := 0x011685a3.
Lemma F_a1ea8 : fetch_word AsanUbsan.M.loaded_segments (0xa1ea8 : word) = Some W_a1ea8.
Proof. vm_refl. Qed.
Lemma D_a1ea8 : decode_any W_a1ea8 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1eac : bv 32 := 0x01068713.
Lemma F_a1eac : fetch_word AsanUbsan.M.loaded_segments (0xa1eac : word) = Some W_a1eac.
Proof. vm_refl. Qed.
Lemma D_a1eac : decode_any W_a1eac = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1eb0 : bv 32 := 0x00568623.
Lemma F_a1eb0 : fetch_word AsanUbsan.M.loaded_segments (0xa1eb0 : word) = Some W_a1eb0.
Proof. vm_refl. Qed.
Lemma D_a1eb0 : decode_any W_a1eb0 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1eb4 : bv 32 := 0x006686a3.
Lemma F_a1eb4 : fetch_word AsanUbsan.M.loaded_segments (0xa1eb4 : word) = Some W_a1eb4.
Proof. vm_refl. Qed.
Lemma D_a1eb4 : decode_any W_a1eb4 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1eb8 : bv 32 := 0x00768723.
Lemma F_a1eb8 : fetch_word AsanUbsan.M.loaded_segments (0xa1eb8 : word) = Some W_a1eb8.
Proof. vm_refl. Qed.
Lemma D_a1eb8 : decode_any W_a1eb8 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ebc : bv 32 := 0x01c687a3.
Lemma F_a1ebc : fetch_word AsanUbsan.M.loaded_segments (0xa1ebc : word) = Some W_a1ebc.
Proof. vm_refl. Qed.
Lemma D_a1ebc : decode_any W_a1ebc = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ec0 : bv 32 := 0x00070693.
Lemma F_a1ec0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ec0 : word) = Some W_a1ec0.
Proof. vm_refl. Qed.
Lemma D_a1ec0 : decode_any W_a1ec0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ec4 : bv 32 := 0x00867713.
Lemma F_a1ec4 : fetch_word AsanUbsan.M.loaded_segments (0xa1ec4 : word) = Some W_a1ec4.
Proof. vm_refl. Qed.
Lemma D_a1ec4 : decode_any W_a1ec4 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ec8 : bv 32 := 0xd20706e3.
Lemma F_a1ec8 : fetch_word AsanUbsan.M.loaded_segments (0xa1ec8 : word) = Some W_a1ec8.
Proof. vm_refl. Qed.
Lemma D_a1ec8 : decode_any W_a1ec8 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ecc : bv 32 := 0x0005c703.
Lemma F_a1ecc : fetch_word AsanUbsan.M.loaded_segments (0xa1ecc : word) = Some W_a1ecc.
Proof. vm_refl. Qed.
Lemma D_a1ecc : decode_any W_a1ecc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ed0 : bv 32 := 0x0015c783.
Lemma F_a1ed0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ed0 : word) = Some W_a1ed0.
Proof. vm_refl. Qed.
Lemma D_a1ed0 : decode_any W_a1ed0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ed4 : bv 32 := 0x0025c803.
Lemma F_a1ed4 : fetch_word AsanUbsan.M.loaded_segments (0xa1ed4 : word) = Some W_a1ed4.
Proof. vm_refl. Qed.
Lemma D_a1ed4 : decode_any W_a1ed4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ed8 : bv 32 := 0x0035c883.
Lemma F_a1ed8 : fetch_word AsanUbsan.M.loaded_segments (0xa1ed8 : word) = Some W_a1ed8.
Proof. vm_refl. Qed.
Lemma D_a1ed8 : decode_any W_a1ed8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1edc : bv 32 := 0x0045c283.
Lemma F_a1edc : fetch_word AsanUbsan.M.loaded_segments (0xa1edc : word) = Some W_a1edc.
Proof. vm_refl. Qed.
Lemma D_a1edc : decode_any W_a1edc = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ee0 : bv 32 := 0x0055c303.
Lemma F_a1ee0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ee0 : word) = Some W_a1ee0.
Proof. vm_refl. Qed.
Lemma D_a1ee0 : decode_any W_a1ee0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ee4 : bv 32 := 0x0065c383.
Lemma F_a1ee4 : fetch_word AsanUbsan.M.loaded_segments (0xa1ee4 : word) = Some W_a1ee4.
Proof. vm_refl. Qed.
Lemma D_a1ee4 : decode_any W_a1ee4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ee8 : bv 32 := 0x0075ce03.
Lemma F_a1ee8 : fetch_word AsanUbsan.M.loaded_segments (0xa1ee8 : word) = Some W_a1ee8.
Proof. vm_refl. Qed.
Lemma D_a1ee8 : decode_any W_a1ee8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1eec : bv 32 := 0x00858593.
Lemma F_a1eec : fetch_word AsanUbsan.M.loaded_segments (0xa1eec : word) = Some W_a1eec.
Proof. vm_refl. Qed.
Lemma D_a1eec : decode_any W_a1eec = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ef0 : bv 32 := 0x00e68023.
Lemma F_a1ef0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ef0 : word) = Some W_a1ef0.
Proof. vm_refl. Qed.
Lemma D_a1ef0 : decode_any W_a1ef0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ef4 : bv 32 := 0x00f680a3.
Lemma F_a1ef4 : fetch_word AsanUbsan.M.loaded_segments (0xa1ef4 : word) = Some W_a1ef4.
Proof. vm_refl. Qed.
Lemma D_a1ef4 : decode_any W_a1ef4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1ef8 : bv 32 := 0x01068123.
Lemma F_a1ef8 : fetch_word AsanUbsan.M.loaded_segments (0xa1ef8 : word) = Some W_a1ef8.
Proof. vm_refl. Qed.
Lemma D_a1ef8 : decode_any W_a1ef8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1efc : bv 32 := 0x011681a3.
Lemma F_a1efc : fetch_word AsanUbsan.M.loaded_segments (0xa1efc : word) = Some W_a1efc.
Proof. vm_refl. Qed.
Lemma D_a1efc : decode_any W_a1efc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f00 : bv 32 := 0x00868713.
Lemma F_a1f00 : fetch_word AsanUbsan.M.loaded_segments (0xa1f00 : word) = Some W_a1f00.
Proof. vm_refl. Qed.
Lemma D_a1f00 : decode_any W_a1f00 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f04 : bv 32 := 0x00568223.
Lemma F_a1f04 : fetch_word AsanUbsan.M.loaded_segments (0xa1f04 : word) = Some W_a1f04.
Proof. vm_refl. Qed.
Lemma D_a1f04 : decode_any W_a1f04 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f08 : bv 32 := 0x006682a3.
Lemma F_a1f08 : fetch_word AsanUbsan.M.loaded_segments (0xa1f08 : word) = Some W_a1f08.
Proof. vm_refl. Qed.
Lemma D_a1f08 : decode_any W_a1f08 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f0c : bv 32 := 0x00768323.
Lemma F_a1f0c : fetch_word AsanUbsan.M.loaded_segments (0xa1f0c : word) = Some W_a1f0c.
Proof. vm_refl. Qed.
Lemma D_a1f0c : decode_any W_a1f0c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f10 : bv 32 := 0x01c683a3.
Lemma F_a1f10 : fetch_word AsanUbsan.M.loaded_segments (0xa1f10 : word) = Some W_a1f10.
Proof. vm_refl. Qed.
Lemma D_a1f10 : decode_any W_a1f10 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f14 : bv 32 := 0x00070693.
Lemma F_a1f14 : fetch_word AsanUbsan.M.loaded_segments (0xa1f14 : word) = Some W_a1f14.
Proof. vm_refl. Qed.
Lemma D_a1f14 : decode_any W_a1f14 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f18 : bv 32 := 0x00467713.
Lemma F_a1f18 : fetch_word AsanUbsan.M.loaded_segments (0xa1f18 : word) = Some W_a1f18.
Proof. vm_refl. Qed.
Lemma D_a1f18 : decode_any W_a1f18 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f1c : bv 32 := 0x02070863.
Lemma F_a1f1c : fetch_word AsanUbsan.M.loaded_segments (0xa1f1c : word) = Some W_a1f1c.
Proof. vm_refl. Qed.
Lemma D_a1f1c : decode_any W_a1f1c = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f20 : bv 32 := 0x0005c703.
Lemma F_a1f20 : fetch_word AsanUbsan.M.loaded_segments (0xa1f20 : word) = Some W_a1f20.
Proof. vm_refl. Qed.
Lemma D_a1f20 : decode_any W_a1f20 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f24 : bv 32 := 0x0015c783.
Lemma F_a1f24 : fetch_word AsanUbsan.M.loaded_segments (0xa1f24 : word) = Some W_a1f24.
Proof. vm_refl. Qed.
Lemma D_a1f24 : decode_any W_a1f24 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f28 : bv 32 := 0x0025c803.
Lemma F_a1f28 : fetch_word AsanUbsan.M.loaded_segments (0xa1f28 : word) = Some W_a1f28.
Proof. vm_refl. Qed.
Lemma D_a1f28 : decode_any W_a1f28 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f2c : bv 32 := 0x0035c883.
Lemma F_a1f2c : fetch_word AsanUbsan.M.loaded_segments (0xa1f2c : word) = Some W_a1f2c.
Proof. vm_refl. Qed.
Lemma D_a1f2c : decode_any W_a1f2c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f30 : bv 32 := 0x00458593.
Lemma F_a1f30 : fetch_word AsanUbsan.M.loaded_segments (0xa1f30 : word) = Some W_a1f30.
Proof. vm_refl. Qed.
Lemma D_a1f30 : decode_any W_a1f30 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f34 : bv 32 := 0x00468293.
Lemma F_a1f34 : fetch_word AsanUbsan.M.loaded_segments (0xa1f34 : word) = Some W_a1f34.
Proof. vm_refl. Qed.
Lemma D_a1f34 : decode_any W_a1f34 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f38 : bv 32 := 0x00e68023.
Lemma F_a1f38 : fetch_word AsanUbsan.M.loaded_segments (0xa1f38 : word) = Some W_a1f38.
Proof. vm_refl. Qed.
Lemma D_a1f38 : decode_any W_a1f38 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f3c : bv 32 := 0x00f680a3.
Lemma F_a1f3c : fetch_word AsanUbsan.M.loaded_segments (0xa1f3c : word) = Some W_a1f3c.
Proof. vm_refl. Qed.
Lemma D_a1f3c : decode_any W_a1f3c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f40 : bv 32 := 0x01068123.
Lemma F_a1f40 : fetch_word AsanUbsan.M.loaded_segments (0xa1f40 : word) = Some W_a1f40.
Proof. vm_refl. Qed.
Lemma D_a1f40 : decode_any W_a1f40 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f44 : bv 32 := 0x011681a3.
Lemma F_a1f44 : fetch_word AsanUbsan.M.loaded_segments (0xa1f44 : word) = Some W_a1f44.
Proof. vm_refl. Qed.
Lemma D_a1f44 : decode_any W_a1f44 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f48 : bv 32 := 0x00028693.
Lemma F_a1f48 : fetch_word AsanUbsan.M.loaded_segments (0xa1f48 : word) = Some W_a1f48.
Proof. vm_refl. Qed.
Lemma D_a1f48 : decode_any W_a1f48 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f4c : bv 32 := 0x00267713.
Lemma F_a1f4c : fetch_word AsanUbsan.M.loaded_segments (0xa1f4c : word) = Some W_a1f4c.
Proof. vm_refl. Qed.
Lemma D_a1f4c : decode_any W_a1f4c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f50 : bv 32 := 0x00071863.
Lemma F_a1f50 : fetch_word AsanUbsan.M.loaded_segments (0xa1f50 : word) = Some W_a1f50.
Proof. vm_refl. Qed.
Lemma D_a1f50 : decode_any W_a1f50 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f54 : bv 32 := 0x00167613.
Lemma F_a1f54 : fetch_word AsanUbsan.M.loaded_segments (0xa1f54 : word) = Some W_a1f54.
Proof. vm_refl. Qed.
Lemma D_a1f54 : decode_any W_a1f54 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f58 : bv 32 := 0x02061663.
Lemma F_a1f58 : fetch_word AsanUbsan.M.loaded_segments (0xa1f58 : word) = Some W_a1f58.
Proof. vm_refl. Qed.
Lemma D_a1f58 : decode_any W_a1f58 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f5c : bv 32 := 0x00008067.
Lemma F_a1f5c : fetch_word AsanUbsan.M.loaded_segments (0xa1f5c : word) = Some W_a1f5c.
Proof. vm_refl. Qed.
Lemma D_a1f5c : decode_any W_a1f5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f60 : bv 32 := 0x0005c703.
Lemma F_a1f60 : fetch_word AsanUbsan.M.loaded_segments (0xa1f60 : word) = Some W_a1f60.
Proof. vm_refl. Qed.
Lemma D_a1f60 : decode_any W_a1f60 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f64 : bv 32 := 0x0015c783.
Lemma F_a1f64 : fetch_word AsanUbsan.M.loaded_segments (0xa1f64 : word) = Some W_a1f64.
Proof. vm_refl. Qed.
Lemma D_a1f64 : decode_any W_a1f64 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f68 : bv 32 := 0x00258593.
Lemma F_a1f68 : fetch_word AsanUbsan.M.loaded_segments (0xa1f68 : word) = Some W_a1f68.
Proof. vm_refl. Qed.
Lemma D_a1f68 : decode_any W_a1f68 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f6c : bv 32 := 0x00268813.
Lemma F_a1f6c : fetch_word AsanUbsan.M.loaded_segments (0xa1f6c : word) = Some W_a1f6c.
Proof. vm_refl. Qed.
Lemma D_a1f6c : decode_any W_a1f6c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f70 : bv 32 := 0x00e68023.
Lemma F_a1f70 : fetch_word AsanUbsan.M.loaded_segments (0xa1f70 : word) = Some W_a1f70.
Proof. vm_refl. Qed.
Lemma D_a1f70 : decode_any W_a1f70 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f74 : bv 32 := 0x00f680a3.
Lemma F_a1f74 : fetch_word AsanUbsan.M.loaded_segments (0xa1f74 : word) = Some W_a1f74.
Proof. vm_refl. Qed.
Lemma D_a1f74 : decode_any W_a1f74 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f78 : bv 32 := 0x00080693.
Lemma F_a1f78 : fetch_word AsanUbsan.M.loaded_segments (0xa1f78 : word) = Some W_a1f78.
Proof. vm_refl. Qed.
Lemma D_a1f78 : decode_any W_a1f78 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f7c : bv 32 := 0x00167613.
Lemma F_a1f7c : fetch_word AsanUbsan.M.loaded_segments (0xa1f7c : word) = Some W_a1f7c.
Proof. vm_refl. Qed.
Lemma D_a1f7c : decode_any W_a1f7c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f80 : bv 32 := 0xfc060ee3.
Lemma F_a1f80 : fetch_word AsanUbsan.M.loaded_segments (0xa1f80 : word) = Some W_a1f80.
Proof. vm_refl. Qed.
Lemma D_a1f80 : decode_any W_a1f80 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f84 : bv 32 := 0x0005c583.
Lemma F_a1f84 : fetch_word AsanUbsan.M.loaded_segments (0xa1f84 : word) = Some W_a1f84.
Proof. vm_refl. Qed.
Lemma D_a1f84 : decode_any W_a1f84 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f88 : bv 32 := 0x00b68023.
Lemma F_a1f88 : fetch_word AsanUbsan.M.loaded_segments (0xa1f88 : word) = Some W_a1f88.
Proof. vm_refl. Qed.
Lemma D_a1f88 : decode_any W_a1f88 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a1f8c : bv 32 := 0x00008067.
Lemma F_a1f8c : fetch_word AsanUbsan.M.loaded_segments (0xa1f8c : word) = Some W_a1f8c.
Proof. vm_refl. Qed.
Lemma D_a1f8c : decode_any W_a1f8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End Bothh6z.

Module Bothpwm.
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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk WalkTac MmapSim RefMocc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothaek OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothh6z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Local Ltac stn_K := constr:(8%nat).
Local Ltac stn_depth R := lazymatch R with regupd ?R' _ _ => let d := stn_depth R' in constr:(S d) | _ => constr:(O) end.
Local Ltac stn_innermost m := lazymatch m with wbytes ?m' _ _ => lazymatch m' with wbytes _ _ _ => stn_innermost m' | _ => m end end.
Local Ltac stn_set t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_mark x).
Local Ltac stn_grow_fact x :=
  let body := eval unfold x in x in
  lazymatch body with wbytes ?p ?a ?bs =>
    let H := fresh "HMG" in
    first [ match goal with Hp : mem_grows ?b0 p |- _ => assert (H : mem_grows b0 x) by (exact (mem_grows_trans b0 p x Hp (wbytes_grows bs p a))) end
          | assert (H : mem_grows p x) by (exact (wbytes_grows bs p a)) ]
  end.
Local Ltac stn_setm t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_markm x); try stn_grow_fact x.
Local Ltac stn_name_regs R :=
  let d := stn_depth R in let k := stn_K in
  lazymatch eval cbv in (Nat.leb k d) with true => stn_set R ident:(RN) | false => idtac end.
Local Ltac stn_name_M :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ ?M _) _ =>
    lazymatch M with wbytes _ _ _ => idtac end;
    let t := stn_innermost M in stn_setm t ident:(MN) end).
(* [comment removed for export] *)
Local Ltac stn_eexists :=
  lazymatch goal with
  | |- @ex (bvmap _ _) _ => eapply stn_ex_by_eq; (let x := fresh "regsW" in let E := fresh "EregsW" in intros x E; pose proof (I : stn_mark E))
  | |- _ => eexists
  end.
Local Ltac stn_wit :=
  repeat match goal with
  | M : stn_mark ?E |- ?g => lazymatch type of E with ?x = _ => lazymatch g with context [x] => rewrite E end end
  end.
Local Ltac stn_begin :=
  lazymatch goal with
  | |- msteps _ _ ?t => tryif is_var t then idtac else (apply stn_msteps_tgt; let s := fresh "stF" in let E := fresh "EstF" in intros s E)
  | |- _ => idtac
  end.
Local Ltac renm :=
  stn_begin;
  lazymatch goal with
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open :=
  repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end;
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end.
Local Ltac stn_done :=
  repeat first [ match goal with H : stn_mark ?x |- ?g => lazymatch g with context [x] => unfold x end end
               | match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end ];
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end;
  stn_wit.
Local Ltac stn_demand1 :=
  match goal with
  | M : stn_mark ?E |- context [getr ?x _] => lazymatch type of E with x = _ => rewrite E end
  | H : getr ?b ?x = _ |- context [getr ?b ?x] => is_var b; (let body := eval unfold b in b in idtac); rewrite !H
  | |- context [getr ?b ?x] =>
      is_var b;
      let body := eval unfold b in b in
      lazymatch body with regupd _ _ _ => idtac end;
      let l := gresl_list body in
      let bb := gresl_base body in
      let v := gresl_val body x in
      let H := fresh "HGN" in
      assert (H : getr b x = v) by (exact (getr_regupds l bb x (@eq_refl bool false)));
      rewrite !H
  end.
(* [comment removed for export] *)
Local Ltac stn_final :=
  try (lazymatch goal with |- _ (mkst ?X _ _ _) =>
         lazymatch X with regupd _ _ _ =>
           let l := gresl_list X in let b := gresl_base X in
           let H := fresh "GRF" in pose proof (getr_regupds l b) as H end end).
Local Ltac stn_final_use :=
  lazymatch goal with |- getr ?X ?r = _ =>
    lazymatch X with regupd _ _ _ =>
      match goal with GRF : (forall r0 : reg, bv_eqb r0 0 = false -> getr (regupds _ _) r0 = _) |- _ => exact (GRF r (@eq_refl bool false)) end end end.
Local Ltac stn_gres_old :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let l := gresl_list X in
             let b := gresl_base X in
             let v := gresl_val X r in
             let p := constr:(getr_regupds l b r (@eq_refl bool false) : getr X r = v) in
             rewrite p
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac.gres ::= first [ stn_final_use | stn_gres_old; repeat (stn_demand1; stn_gres_old) ].
Local Ltac stn_sok_old :=
  lazymatch goal with
  | |- store_ok ?segs ?M ?a ?n = true =>
      let b := sokl_base M in
      lazymatch b with
      | M => idtac
      | _ => let l := sokl_list M in
             refine ((store_ok_layers segs n l b a _) : store_ok segs M a n = true)
      end
  | |- _ => idtac
  end.
Local Ltac stn_sok_named :=
  lazymatch goal with |- store_ok ?segs ?M ?a ?n = true =>
    is_var M; match goal with H : mem_grows ?b M |- _ => apply (store_ok_mono segs n b M a H) end end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.store_ok_peel ::= stn_sok_old; try stn_sok_named.

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Section AL.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b1_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    (0 <= k)%Z -> (k + 1 = n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1f84 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    stn_eexists. split.
    - mlbu F_a1f84 D_a1f84 k.                      (* [comment removed for export] *)
      renm. msb F_a1f88 D_a1f88 k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
      stn_open. replace (k + 1)%Z with n by lia.
      renm. stepret F_a1f8c D_a1f8c ret ltac:(exact H1).
      stn_done. apply mst_refl.
    - solve_keeps.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t2_run : forall regs (ret : word) k m,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z ->
    (Z.land m 2 = 0 \/ Z.land m 2 = 2)%Z -> (Z.land m 1 = 0 \/ Z.land m 1 = 1)%Z ->
    (0 <= k)%Z -> (n - k = Z.land m 2 + Z.land m 1)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1f4c : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. stepn F_a1f4c D_a1f4c.                          (* [comment removed for export] *)
        renm. stepb_ft F_a1f50 D_a1f50 ltac:(cond).           (* [comment removed for export] *)
        renm. stepn F_a1f54 D_a1f54.                          (* [comment removed for export] *)
        renm. stepb_ft F_a1f58 D_a1f58 ltac:(cond).           (* [comment removed for export] *)
        renm. stepret F_a1f5c D_a1f5c ret ltac:(exact H1).
        stn_done. mk_eq. stn_done. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1f84 : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1f4c D_a1f4c.
          renm. stepb_ft F_a1f50 D_a1f50 ltac:(cond).
          renm. stepn F_a1f54 D_a1f54.
          renm. stepb_tk F_a1f58 D_a1f58 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. (intros r1; (first [ intro dR_11; dand4 dR_11 as R1 R11 R13 K1 | intros (R1 & R11 & R13 & K1) ])).
        (first [ pose proof ((b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; destruct dR_1 as [RUN K2] | pose proof ((b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia))) as dR_1; dand3 dR_1 as r2 RUN K2 | destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2) ]).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. stepn F_a1f4c D_a1f4c.
        renm. stepb_tk F_a1f50 D_a1f50 ltac:(cond).           (* [comment removed for export] *)
        mlbu F_a1f60 D_a1f60 k.                         (* [comment removed for export] *)
        mlbu F_a1f64 D_a1f64 (k + 1)%Z.                 (* [comment removed for export] *)
        renm. stepn F_a1f68 D_a1f68.                          (* [comment removed for export] *)
        renm. stepn F_a1f6c D_a1f6c.                          (* [comment removed for export] *)
        renm. msb F_a1f70 D_a1f70 k ltac:(apply sb_val_plain).          (* [comment removed for export] *)
        renm. msb F_a1f74 D_a1f74 (k + 1)%Z ltac:(apply sb_val_plain).  (* [comment removed for export] *)
        renm. stepn F_a1f78 D_a1f78.                          (* [comment removed for export] *)
        renm. stepn F_a1f7c D_a1f7c.                          (* [comment removed for export] *)
        renm. stepb_tk F_a1f80 D_a1f80 ltac:(cond).           (* [comment removed for export] *)
        renm. stepret F_a1f5c D_a1f5c ret ltac:(exact H1).
        stn_done. mk_eq. stn_done. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1f84 : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1f4c D_a1f4c.
          renm. stepb_tk F_a1f50 D_a1f50 ltac:(cond).
          mlbu F_a1f60 D_a1f60 k.
          mlbu F_a1f64 D_a1f64 (k + 1)%Z.
          renm. stepn F_a1f68 D_a1f68.
          renm. stepn F_a1f6c D_a1f6c.
          renm. msb F_a1f70 D_a1f70 k ltac:(apply sb_val_plain).
          renm. msb F_a1f74 D_a1f74 (k + 1)%Z ltac:(apply sb_val_plain).
          renm. stepn F_a1f78 D_a1f78.
          renm. stepn F_a1f7c D_a1f7c.
          renm. stepb_ft F_a1f80 D_a1f80 ltac:(cond).         (* [comment removed for export] *)
          stn_done. mk_eq. stn_done. apply mst_refl.
        * cbv beta. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. (intros r1; (first [ intro dR_12; dand4 dR_12 as R1 R11 R13 K1 | intros (R1 & R11 & R13 & K1) ])).
        (first [ pose proof ((b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia))) as dR_2; dex1 dR_2 as r2; destruct dR_2 as [RUN K2] | pose proof ((b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia))) as dR_2; dand3 dR_2 as r2 RUN K2 | destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2) ]).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al4_run : forall regs (ret : word) k m,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1d08 : word) (MK k) rom)
                   (mkst regs' (0xa1f4c : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 4) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - stn_eexists. split.
      + renm. stepn F_a1d08 D_a1d08.                          (* [comment removed for export] *)
        renm. stepb_tk F_a1d0c D_a1d0c ltac:(cond).           (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - stn_eexists. split.
      + renm. stepn F_a1d08 D_a1d08.
        renm. stepb_ft F_a1d0c D_a1d0c ltac:(cond).           (* [comment removed for export] *)
        renm. mlw F_a1d10 D_a1d10 k.                          (* [comment removed for export] *)
        renm. stepn F_a1d14 D_a1d14.                          (* [comment removed for export] *)
        renm. msw F_a1d18 D_a1d18 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).   (* [comment removed for export] *)
        renm. stepn F_a1d1c D_a1d1c.                          (* [comment removed for export] *)
        renm. stepn F_a1d20 D_a1d20.                          (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al8_run : forall regs (ret : word) k m e8,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (m < 8 /\ e8 = 0 \/ 8 <= m /\ e8 = 8 /\ k + 8 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1ce8 : word) (MK k) rom)
                   (mkst regs' (0xa1d08 : word) (MK (k + e8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + e8)
      /\ getr regs' 13 = at_ dst (k + e8) /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - stn_eexists. split.
      + renm. stepn F_a1ce8 D_a1ce8.                          (* [comment removed for export] *)
        renm. stepb_tk F_a1cec D_a1cec ltac:(cond).           (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - stn_eexists. split.
      + renm. stepn F_a1ce8 D_a1ce8.
        renm. stepb_ft F_a1cec D_a1cec ltac:(cond).
        renm. mlw F_a1cf0 D_a1cf0 k.                          (* [comment removed for export] *)
        renm. mlw F_a1cf4 D_a1cf4 (k + 4)%Z.                  (* [comment removed for export] *)
        renm. msw F_a1cf8 D_a1cf8 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
        renm. msw F_a1cfc D_a1cfc (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        renm. stepn F_a1d00 D_a1d00.                          (* [comment removed for export] *)
        renm. stepn F_a1d04 D_a1d04.                          (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_loop : forall (q : nat) regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = Z_to_bv 64 15 ->
    (0 <= k)%Z -> (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1cb8 : word) (MK k) rom)
                   (mkst regs' (0xa1ce8 : word) (MK (k + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 13 = at_ dst (k + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. mlw F_a1cb8 D_a1cb8 k.                          (* [comment removed for export] *)
        renm. mlw F_a1cbc D_a1cbc (k + 4)%Z.                  (* [comment removed for export] *)
        renm. mlw F_a1cc0 D_a1cc0 (k + 8)%Z.                  (* [comment removed for export] *)
        renm. mlw F_a1cc4 D_a1cc4 (k + 12)%Z.                 (* [comment removed for export] *)
        renm. stepn F_a1cc8 D_a1cc8.                          (* [comment removed for export] *)
        renm. stepn F_a1ccc D_a1ccc.                          (* [comment removed for export] *)
        renm. msw F_a1cd0 D_a1cd0 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).          (* [comment removed for export] *)
        renm. msw F_a1cd4 D_a1cd4 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        renm. msw F_a1cd8 D_a1cd8 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        renm. msw F_a1cdc D_a1cdc (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        renm. stepn F_a1ce0 D_a1ce0.                          (* [comment removed for export] *)
        renm. stepb_ft F_a1ce4 D_a1ce4 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * stn_open. unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1cb8 : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. mlw F_a1cb8 D_a1cb8 k.
          renm. mlw F_a1cbc D_a1cbc (k + 4)%Z.
          renm. mlw F_a1cc0 D_a1cc0 (k + 8)%Z.
          renm. mlw F_a1cc4 D_a1cc4 (k + 12)%Z.
          renm. stepn F_a1cc8 D_a1cc8.
          renm. stepn F_a1ccc D_a1ccc.
          renm. msw F_a1cd0 D_a1cd0 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. msw F_a1cd4 D_a1cd4 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. msw F_a1cd8 D_a1cd8 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. msw F_a1cdc D_a1cdc (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          renm. stepn F_a1ce0 D_a1ce0.
          renm. stepb_tk F_a1ce4 D_a1ce4 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          stn_done. mk_eq. stn_done. apply mst_refl.
        * cbv beta. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
          -- stn_open. unfold v_addi. unorm. f_equal. lia.
          -- solve_keeps.
      + cbv beta. (intros r1; (first [ intro dR_13; dand6 dR_13 as R1 R11 R13 R12 R14 K1 | intros (R1 & R11 & R13 & R12 & R14 & K1) ])).
        (first [ pose proof ((IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia))) as dR_3; dex1 dR_3 as r2; destruct dR_3 as [RUN P] | pose proof ((IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia))) as dR_3; dand3 dR_3 as r2 RUN P | destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. split.
        * stn_open. replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
        * stn_open. replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
          decompose [and] P. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma al16_run : forall regs (ret : word) k,
    getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1cac : word) (MK k) rom)
                   (mkst regs' (0xa1ce8 : word) (MK (n - (n - k) mod 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (n - k) mod 16)
      /\ getr regs' 13 = at_ dst (n - (n - k) mod 16)
      /\ getr regs' 12 = Z_to_bv 64 ((n - k) mod 16) /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      stn_eexists. split.
      + renm. stepn F_a1cac D_a1cac.                          (* [comment removed for export] *)
        renm. stepb_tk F_a1cb0 D_a1cb0 ltac:(cond).           (* [comment removed for export] *)
        stn_open. replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
        stn_done. apply mst_refl.
      + stn_open. rewrite (Z.mod_small (n - k) 16) by lia. stn_open. replace (n - (n - k))%Z with k by lia.
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; try reflexivity. solve_keeps.
    - set (q := Z.to_nat ((n - k) / 16 - 1)).
      assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
      { subst q. stn_open. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
      assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
      { subst q. stn_open. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1cb8 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1cac D_a1cac.                        (* [comment removed for export] *)
          renm. stepb_ft F_a1cb0 D_a1cb0 ltac:(cond).         (* [comment removed for export] *)
          renm. stepn F_a1cb4 D_a1cb4.                        (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. (intros r1; (first [ intro dR_14; dand6 dR_14 as R1 R11 R13 R12 R14 K1 | intros (R1 & R11 & R13 & R12 & R14 & K1) ])).
        (first [ pose proof ((al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq)) as dR_4; dex1 dR_4 as r2; destruct dR_4 as [RUN P] | pose proof ((al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq)) as dR_4; dand3 dR_4 as r2 RUN P | destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite <- Hk'. stn_open. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Bothpwm.

Module Bothz8e.
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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk WalkTac MmapSim RefMocc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothaek OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothpwm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothh6z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Local Ltac stn_K := constr:(8%nat).
Local Ltac stn_depth R := lazymatch R with regupd ?R' _ _ => let d := stn_depth R' in constr:(S d) | _ => constr:(O) end.
Local Ltac stn_innermost m := lazymatch m with wbytes ?m' _ _ => lazymatch m' with wbytes _ _ _ => stn_innermost m' | _ => m end end.
Local Ltac stn_set t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_mark x).
Local Ltac stn_grow_fact x :=
  let body := eval unfold x in x in
  lazymatch body with wbytes ?p ?a ?bs =>
    let H := fresh "HMG" in
    first [ match goal with Hp : mem_grows ?b0 p |- _ => assert (H : mem_grows b0 x) by (exact (mem_grows_trans b0 p x Hp (wbytes_grows bs p a))) end
          | assert (H : mem_grows p x) by (exact (wbytes_grows bs p a)) ]
  end.
Local Ltac stn_setm t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_markm x); try stn_grow_fact x.
Local Ltac stn_name_regs R :=
  let d := stn_depth R in let k := stn_K in
  lazymatch eval cbv in (Nat.leb k d) with true => stn_set R ident:(RN) | false => idtac end.
Local Ltac stn_name_M :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ ?M _) _ =>
    lazymatch M with wbytes _ _ _ => idtac end;
    let t := stn_innermost M in stn_setm t ident:(MN) end).
(* [comment removed for export] *)
Local Ltac stn_eexists :=
  lazymatch goal with
  | |- @ex (bvmap _ _) _ => eapply stn_ex_by_eq; (let x := fresh "regsW" in let E := fresh "EregsW" in intros x E; pose proof (I : stn_mark E))
  | |- _ => eexists
  end.
Local Ltac stn_wit :=
  repeat match goal with
  | M : stn_mark ?E |- ?g => lazymatch type of E with ?x = _ => lazymatch g with context [x] => rewrite E end end
  end.
Local Ltac stn_begin :=
  lazymatch goal with
  | |- msteps _ _ ?t => tryif is_var t then idtac else (apply stn_msteps_tgt; let s := fresh "stF" in let E := fresh "EstF" in intros s E)
  | |- _ => idtac
  end.
Local Ltac renm :=
  stn_begin;
  lazymatch goal with
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
Local Ltac stn_done :=
  repeat first [ match goal with H : stn_mark ?x |- ?g => lazymatch g with context [x] => unfold x end end
               | match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end ];
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end;
  stn_wit.
Local Ltac stn_demand1 :=
  match goal with
  | M : stn_mark ?E |- context [getr ?x _] => lazymatch type of E with x = _ => rewrite E end
  | H : getr ?b ?x = _ |- context [getr ?b ?x] => is_var b; (let body := eval unfold b in b in idtac); rewrite !H
  | |- context [getr ?b ?x] =>
      is_var b;
      let body := eval unfold b in b in
      lazymatch body with regupd _ _ _ => idtac end;
      let l := gresl_list body in
      let bb := gresl_base body in
      let v := gresl_val body x in
      let H := fresh "HGN" in
      assert (H : getr b x = v) by (exact (getr_regupds l bb x (@eq_refl bool false)));
      rewrite !H
  end.
Local Ltac stn_gres_old :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let l := gresl_list X in
             let b := gresl_base X in
             let v := gresl_val X r in
             let p := constr:(getr_regupds l b r (@eq_refl bool false) : getr X r = v) in
             rewrite p
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac.gres ::= stn_gres_old; repeat (stn_demand1; stn_gres_old).
Local Ltac stn_sok_old :=
  lazymatch goal with
  | |- store_ok ?segs ?M ?a ?n = true =>
      let b := sokl_base M in
      lazymatch b with
      | M => idtac
      | _ => let l := sokl_list M in
             refine ((store_ok_layers segs n l b a _) : store_ok segs M a n = true)
      end
  | |- _ => idtac
  end.
Local Ltac stn_sok_named :=
  lazymatch goal with |- store_ok ?segs ?M ?a ?n = true =>
    is_var M; match goal with H : mem_grows ?b M |- _ => apply (store_ok_mono segs n b M a H) end end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.store_ok_peel ::= stn_sok_old; try stn_sok_named.

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Section MIS.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac sbp := apply sb_val_plain.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma b4_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1f20 : word) (MK k) rom) (mkst regs' (0xa1f4c : word) (MK (k + 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 4) /\ getr regs' 13 = at_ dst (k + 4)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. stn_eexists. split.
    - mlbu F_a1f20 D_a1f20 k. mlbu F_a1f24 D_a1f24 (k+1)%Z. mlbu F_a1f28 D_a1f28 (k+2)%Z. mlbu F_a1f2c D_a1f2c (k+3)%Z.
      renm. stepn F_a1f30 D_a1f30.                            (* [comment removed for export] *)
      renm. stepn F_a1f34 D_a1f34.                            (* [comment removed for export] *)
      renm. msb F_a1f38 D_a1f38 k ltac:(sbp). renm. msb F_a1f3c D_a1f3c (k+1)%Z ltac:(sbp).
      renm. msb F_a1f40 D_a1f40 (k+2)%Z ltac:(sbp). renm. msb F_a1f44 D_a1f44 (k+3)%Z ltac:(sbp).
      renm. stepn F_a1f48 D_a1f48.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 8 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1ecc : word) (MK k) rom) (mkst regs' (0xa1f18 : word) (MK (k + 8)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 8) /\ getr regs' 13 = at_ dst (k + 8)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. stn_eexists. split.
    - mlbu F_a1ecc D_a1ecc k. mlbu F_a1ed0 D_a1ed0 (k+1)%Z. mlbu F_a1ed4 D_a1ed4 (k+2)%Z. mlbu F_a1ed8 D_a1ed8 (k+3)%Z.
      mlbu F_a1edc D_a1edc (k+4)%Z. mlbu F_a1ee0 D_a1ee0 (k+5)%Z. mlbu F_a1ee4 D_a1ee4 (k+6)%Z. mlbu F_a1ee8 D_a1ee8 (k+7)%Z.
      renm. stepn F_a1eec D_a1eec.                            (* [comment removed for export] *)
      renm. msb F_a1ef0 D_a1ef0 k ltac:(sbp). renm. msb F_a1ef4 D_a1ef4 (k+1)%Z ltac:(sbp).
      renm. msb F_a1ef8 D_a1ef8 (k+2)%Z ltac:(sbp). renm. msb F_a1efc D_a1efc (k+3)%Z ltac:(sbp).
      renm. stepn F_a1f00 D_a1f00.                            (* [comment removed for export] *)
      renm. msb F_a1f04 D_a1f04 (k+4)%Z ltac:(sbp). renm. msb F_a1f08 D_a1f08 (k+5)%Z ltac:(sbp).
      renm. msb F_a1f0c D_a1f0c (k+6)%Z ltac:(sbp). renm. msb F_a1f10 D_a1f10 (k+7)%Z ltac:(sbp).
      renm. stepn F_a1f14 D_a1f14.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_blk : forall regs (ret : word) k (a2 : word),
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = a2 ->
    (0 <= k)%Z -> (k + 16 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1e38 : word) (MK k) rom) (mkst regs' (0xa1ec4 : word) (MK (k + 16)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 16)
      /\ getr regs' 12 = a2 /\ keeps regs regs'.
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. stn_eexists. split.
    - mlbu F_a1e38 D_a1e38 k. mlbu F_a1e3c D_a1e3c (k+1)%Z. mlbu F_a1e40 D_a1e40 (k+2)%Z. mlbu F_a1e44 D_a1e44 (k+3)%Z.
      mlbu F_a1e48 D_a1e48 (k+4)%Z. mlbu F_a1e4c D_a1e4c (k+5)%Z. mlbu F_a1e50 D_a1e50 (k+6)%Z. mlbu F_a1e54 D_a1e54 (k+7)%Z.
      renm. msb F_a1e58 D_a1e58 k ltac:(sbp). renm. msb F_a1e5c D_a1e5c (k+1)%Z ltac:(sbp).
      renm. msb F_a1e60 D_a1e60 (k+2)%Z ltac:(sbp). renm. msb F_a1e64 D_a1e64 (k+3)%Z ltac:(sbp).
      mlbu F_a1e68 D_a1e68 (k+8)%Z. mlbu F_a1e6c D_a1e6c (k+9)%Z. mlbu F_a1e70 D_a1e70 (k+10)%Z. mlbu F_a1e74 D_a1e74 (k+11)%Z.
      renm. msb F_a1e78 D_a1e78 (k+4)%Z ltac:(sbp). renm. msb F_a1e7c D_a1e7c (k+5)%Z ltac:(sbp).
      renm. msb F_a1e80 D_a1e80 (k+6)%Z ltac:(sbp). renm. msb F_a1e84 D_a1e84 (k+7)%Z ltac:(sbp).
      mlbu F_a1e88 D_a1e88 (k+12)%Z. mlbu F_a1e8c D_a1e8c (k+13)%Z. mlbu F_a1e90 D_a1e90 (k+14)%Z. mlbu F_a1e94 D_a1e94 (k+15)%Z.
      renm. stepn F_a1e98 D_a1e98.                            (* [comment removed for export] *)
      renm. msb F_a1e9c D_a1e9c (k+8)%Z ltac:(sbp). renm. msb F_a1ea0 D_a1ea0 (k+9)%Z ltac:(sbp).
      renm. msb F_a1ea4 D_a1ea4 (k+10)%Z ltac:(sbp). renm. msb F_a1ea8 D_a1ea8 (k+11)%Z ltac:(sbp).
      renm. stepn F_a1eac D_a1eac.                            (* [comment removed for export] *)
      renm. msb F_a1eb0 D_a1eb0 (k+12)%Z ltac:(sbp). renm. msb F_a1eb4 D_a1eb4 (k+13)%Z ltac:(sbp).
      renm. msb F_a1eb8 D_a1eb8 (k+14)%Z ltac:(sbp). renm. msb F_a1ebc D_a1ebc (k+15)%Z ltac:(sbp).
      renm. stepn F_a1ec0 D_a1ec0.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma t4_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1bf4 : word) (MK k) rom) (mkst regs' (0xa1f4c : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - stn_eexists. split.
      + renm. stepn F_a1bf4 D_a1bf4.                          (* [comment removed for export] *)
        renm. stepb_ft F_a1bf8 D_a1bf8 ltac:(cond).           (* [comment removed for export] *)
        renm. stepn F_a1bfc D_a1bfc.                          (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + post.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1f20 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1bf4 D_a1bf4.
          renm. stepb_tk F_a1bf8 D_a1bf8 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_13; dand5 dR_13 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; destruct dR_1 as [RUN P] | pose proof ((b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_1; dand3 dR_1 as r2 RUN P | destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b8_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 4 = 0 \/ Z.land m 4 = 4 /\ k + 4 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1f18 : word) (MK k) rom) (mkst regs' (0xa1f4c : word) (MK (k + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 4) /\ getr regs' 13 = at_ dst (k + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - stn_eexists. split.
      + renm. stepn F_a1f18 D_a1f18.                          (* [comment removed for export] *)
        renm. stepb_tk F_a1f1c D_a1f1c ltac:(cond).           (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + post.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1f20 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1f18 D_a1f18.
          renm. stepb_ft F_a1f1c D_a1f1c ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_14; dand5 dR_14 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_2; dex1 dR_2 as r2; destruct dR_2 as [RUN P] | pose proof ((b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_2; dand3 dR_2 as r2 RUN P | destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t8_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1bec : word) (MK k) rom)
                   (mkst regs' (0xa1f4c : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1bf4 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1bec D_a1bec.                        (* [comment removed for export] *)
          renm. stepb_ft F_a1bf0 D_a1bf0 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_15; dand5 dR_15 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia))) as dR_3; dex1 dR_3 as r2; destruct dR_3 as [RUN P] | pose proof ((t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia))) as dR_3; dand3 dR_3 as r2 RUN P | destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1ecc : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1bec D_a1bec.
          renm. stepb_tk F_a1bf0 D_a1bf0 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_16; dand5 dR_16 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1f18 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * (first [ pose proof ((b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as r2; destruct dR_4 as [RUN P] | pose proof ((b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dand3 dR_4 as r2 RUN P | destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_17; dand5 dR_17 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia))) as dR_5; dex1 dR_5 as r3; destruct dR_5 as [RUN P] | pose proof ((b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia))) as dR_5; dand3 dR_5 as r3 RUN P | destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL8. stn_open. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
          split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma b16_tail : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 2 ^ 64)%Z -> (0 <= k)%Z ->
    (Z.land m 8 = 0 \/ Z.land m 8 = 8)%Z -> (Z.land m 4 = 0 \/ Z.land m 4 = 4)%Z ->
    (k + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1ec4 : word) (MK k) rom)
                   (mkst regs' (0xa1f4c : word) (MK (k + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1bf4 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1ec4 D_a1ec4.                        (* [comment removed for export] *)
          renm. stepb_tk F_a1ec8 D_a1ec8 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_18; dand5 dR_18 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia))) as dR_6; dex1 dR_6 as r2; destruct dR_6 as [RUN P] | pose proof ((t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia))) as dR_6; dand3 dR_6 as r2 RUN P | destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1ecc : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1ec4 D_a1ec4.
          renm. stepb_ft F_a1ec8 D_a1ec8 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_19; dand5 dR_19 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1f18 : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * (first [ pose proof ((b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_7; dex1 dR_7 as r2; destruct dR_7 as [RUN P] | pose proof ((b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_7; dand3 dR_7 as r2 RUN P | destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_20; dand5 dR_20 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia))) as dR_8; dex1 dR_8 as r3; destruct dR_8 as [RUN P] | pose proof ((b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia))) as dR_8; dand3 dR_8 as r3 RUN P | destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma t16_run : forall regs (ret : word) k m,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 m ->
    (0 <= m < 32)%Z -> (0 <= k)%Z ->
    (k + Z.land m 16 + Z.land m 8 + Z.land m 4 <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1be4 : word) (MK k) rom)
                   (mkst regs' (0xa1f4c : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
    (first [ pose proof ((bits_lt32 m Hm)) as dR_9; dand6 dR_9 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1bec : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1be4 D_a1be4.                        (* [comment removed for export] *)
          renm. stepb_ft F_a1be8 D_a1be8 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_21; dand5 dR_21 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia))) as dR_10; dex1 dR_10 as r2; destruct dR_10 as [RUN P] | pose proof ((t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia))) as dR_10; dand3 dR_10 as r2 RUN P | destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1e38 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1be4 D_a1be4.
          renm. stepb_tk F_a1be8 D_a1be8 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_22; dand5 dR_22 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1ec4 : word) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * (first [ pose proof ((b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_11; dex1 dR_11 as r2; destruct dR_11 as [RUN P] | pose proof ((b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_11; dand3 dR_11 as r2 RUN P | destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_23; dand5 dR_23 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_12; dex1 dR_12 as r3; destruct dR_12 as [RUN P] | pose proof ((b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_12; dand3 dR_12 as r3 RUN P | destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Bothz8e.

Module Bothe0z.
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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk WalkTac MmapSim RefMocc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothaek OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothpwm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothz8e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothh6z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Local Ltac stn_K := constr:(8%nat).
Local Ltac stn_depth R := lazymatch R with regupd ?R' _ _ => let d := stn_depth R' in constr:(S d) | _ => constr:(O) end.
Local Ltac stn_innermost m := lazymatch m with wbytes ?m' _ _ => lazymatch m' with wbytes _ _ _ => stn_innermost m' | _ => m end end.
Local Ltac stn_set t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_mark x).
Local Ltac stn_grow_fact x :=
  let body := eval unfold x in x in
  lazymatch body with wbytes ?p ?a ?bs =>
    let H := fresh "HMG" in
    first [ match goal with Hp : mem_grows ?b0 p |- _ => assert (H : mem_grows b0 x) by (exact (mem_grows_trans b0 p x Hp (wbytes_grows bs p a))) end
          | assert (H : mem_grows p x) by (exact (wbytes_grows bs p a)) ]
  end.
Local Ltac stn_setm t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_markm x); try stn_grow_fact x.
Local Ltac stn_name_regs R :=
  let d := stn_depth R in let k := stn_K in
  lazymatch eval cbv in (Nat.leb k d) with true => stn_set R ident:(RN) | false => idtac end.
Local Ltac stn_name_M :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ ?M _) _ =>
    lazymatch M with wbytes _ _ _ => idtac end;
    let t := stn_innermost M in stn_setm t ident:(MN) end).
(* [comment removed for export] *)
Local Ltac stn_eexists :=
  lazymatch goal with
  | |- @ex (bvmap _ _) _ => eapply stn_ex_by_eq; (let x := fresh "regsW" in let E := fresh "EregsW" in intros x E; pose proof (I : stn_mark E))
  | |- _ => eexists
  end.
Local Ltac stn_wit :=
  repeat match goal with
  | M : stn_mark ?E |- ?g => lazymatch type of E with ?x = _ => lazymatch g with context [x] => rewrite E end end
  end.
Local Ltac stn_begin :=
  lazymatch goal with
  | |- msteps _ _ ?t => tryif is_var t then idtac else (apply stn_msteps_tgt; let s := fresh "stF" in let E := fresh "EstF" in intros s E)
  | |- _ => idtac
  end.
Local Ltac renm :=
  stn_begin;
  lazymatch goal with
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
Local Ltac stn_done :=
  repeat first [ match goal with H : stn_mark ?x |- ?g => lazymatch g with context [x] => unfold x end end
               | match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end ];
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end;
  stn_wit.
Local Ltac stn_demand1 :=
  match goal with
  | M : stn_mark ?E |- context [getr ?x _] => lazymatch type of E with x = _ => rewrite E end
  | H : getr ?b ?x = _ |- context [getr ?b ?x] => is_var b; (let body := eval unfold b in b in idtac); rewrite !H
  | |- context [getr ?b ?x] =>
      is_var b;
      let body := eval unfold b in b in
      lazymatch body with regupd _ _ _ => idtac end;
      let l := gresl_list body in
      let bb := gresl_base body in
      let v := gresl_val body x in
      let H := fresh "HGN" in
      assert (H : getr b x = v) by (exact (getr_regupds l bb x (@eq_refl bool false)));
      rewrite !H
  end.
Local Ltac stn_gres_old :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let l := gresl_list X in
             let b := gresl_base X in
             let v := gresl_val X r in
             let p := constr:(getr_regupds l b r (@eq_refl bool false) : getr X r = v) in
             rewrite p
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac.gres ::= stn_gres_old; repeat (stn_demand1; stn_gres_old).
Local Ltac stn_sok_old :=
  lazymatch goal with
  | |- store_ok ?segs ?M ?a ?n = true =>
      let b := sokl_base M in
      lazymatch b with
      | M => idtac
      | _ => let l := sokl_list M in
             refine ((store_ok_layers segs n l b a _) : store_ok segs M a n = true)
      end
  | |- _ => idtac
  end.
Local Ltac stn_sok_named :=
  lazymatch goal with |- store_ok ?segs ?M ?a ?n = true =>
    is_var M; match goal with H : mem_grows ?b M |- _ => apply (store_ok_mono segs n b M a H) end end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.store_ok_peel ::= stn_sok_old; try stn_sok_named.

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Section C1.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac m24 := eapply (merge_s24 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  Lemma c1_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1c00 : word) (MK k) rom) (mkst regs' (0xa1dcc : word) (MK (k + 3)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 3)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 3)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 16 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. stn_eexists. split.
    - renm. mlw F_a1c00 D_a1c00 k.                            (* [comment removed for export] *)
      renm. stepn F_a1c04 D_a1c04.                            (* [comment removed for export] *)
      renm. stepb_ft F_a1c08 D_a1c08 ltac:(cond).             (* [comment removed for export] *)
      renm. stepn F_a1c0c D_a1c0c.                            (* [comment removed for export] *)
      renm. stepb_tk F_a1c10 D_a1c10 ltac:(cond).             (* [comment removed for export] *)
      renm. stepn F_a1da8 D_a1da8.                            (* [comment removed for export] *)
      renm. stepn F_a1dac D_a1dac.                            (* [comment removed for export] *)
      renm. stepn F_a1db0 D_a1db0.                            (* [comment removed for export] *)
      renm. msb F_a1db4 D_a1db4 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
      renm. msb F_a1db8 D_a1db8 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
      renm. msb F_a1dbc D_a1dbc (k + 2)%Z ltac:(eapply (sb_val_srli16 _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
      renm. stepn F_a1dc0 D_a1dc0.                            (* [comment removed for export] *)
      renm. stepn F_a1dc4 D_a1dc4.                            (* [comment removed for export] *)
      renm. stepn F_a1dc8 D_a1dc8.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post. stn_open. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c1_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 16 ->
    (ja = kk + 13)%Z -> (jw = kk - 3)%Z -> (3 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 1 <= n - kk < 16 * (Z.of_nat q + 1) + 17)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1dcc : word) (MK kk) rom)
                   (mkst regs' (0xa1e2c : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 13)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - stn_eexists. split.
      + renm. stepn F_a1dcc D_a1dcc.                          (* [comment removed for export] *)
        renm. mlw F_a1dd0 D_a1dd0 (kk + 1)%Z.                 (* [comment removed for export] *)
        renm. mlw F_a1dd4 D_a1dd4 (kk + 5)%Z.                 (* [comment removed for export] *)
        renm. mlw F_a1dd8 D_a1dd8 (kk + 9)%Z.                 (* [comment removed for export] *)
        renm. mlw F_a1ddc D_a1ddc (kk + 13)%Z.                (* [comment removed for export] *)
        renm. stepn F_a1de0 D_a1de0. renm. stepn F_a1de4 D_a1de4. renm. stepn F_a1de8 D_a1de8.
        renm. stepn F_a1dec D_a1dec. renm. stepn F_a1df0 D_a1df0. renm. stepn F_a1df4 D_a1df4.
        renm. stepn F_a1df8 D_a1df8. renm. stepn F_a1dfc D_a1dfc. renm. stepn F_a1e00 D_a1e00.
        renm. stepn F_a1e04 D_a1e04. renm. stepn F_a1e08 D_a1e08.
        renm. stepn F_a1e0c D_a1e0c.                          (* [comment removed for export] *)
        renm. msw F_a1e10 D_a1e10 kk ltac:(m24).
        renm. msw F_a1e14 D_a1e14 (kk + 4)%Z ltac:(m24).
        renm. msw F_a1e18 D_a1e18 (kk + 8)%Z ltac:(m24).
        renm. msw F_a1e1c D_a1e1c (kk + 12)%Z ltac:(m24).
        renm. stepn F_a1e20 D_a1e20.                          (* [comment removed for export] *)
        renm. stepn F_a1e24 D_a1e24.                          (* [comment removed for export] *)
        renm. stepb_ft F_a1e28 D_a1e28 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + post. stn_open. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1dcc : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 13) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 13) 4)
                         /\ getr r 15 = Z_to_bv 64 16 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1dcc D_a1dcc.
          renm. mlw F_a1dd0 D_a1dd0 (kk + 1)%Z.
          renm. mlw F_a1dd4 D_a1dd4 (kk + 5)%Z.
          renm. mlw F_a1dd8 D_a1dd8 (kk + 9)%Z.
          renm. mlw F_a1ddc D_a1ddc (kk + 13)%Z.
          renm. stepn F_a1de0 D_a1de0. renm. stepn F_a1de4 D_a1de4. renm. stepn F_a1de8 D_a1de8.
          renm. stepn F_a1dec D_a1dec. renm. stepn F_a1df0 D_a1df0. renm. stepn F_a1df4 D_a1df4.
          renm. stepn F_a1df8 D_a1df8. renm. stepn F_a1dfc D_a1dfc. renm. stepn F_a1e00 D_a1e00.
          renm. stepn F_a1e04 D_a1e04. renm. stepn F_a1e08 D_a1e08.
          renm. stepn F_a1e0c D_a1e0c.
          renm. msw F_a1e10 D_a1e10 kk ltac:(m24).
          renm. msw F_a1e14 D_a1e14 (kk + 4)%Z ltac:(m24).
          renm. msw F_a1e18 D_a1e18 (kk + 8)%Z ltac:(m24).
          renm. msw F_a1e1c D_a1e1c (kk + 12)%Z ltac:(m24).
          renm. stepn F_a1e20 D_a1e20.
          renm. stepn F_a1e24 D_a1e24.
          renm. stepb_tk F_a1e28 D_a1e28 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          stn_done. mk_eq. stn_done. apply mst_refl.
        * cbv beta. post. stn_open. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. (intros r1; (first [ intro dR_10; dand7 dR_10 as R1 R11 R13 R12 R14 R15 K1 | intros (R1 & R11 & R13 & R12 & R14 & R15 & K1) ])).
        (first [ pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; destruct dR_1 as [RUN P] | pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dand3 dR_1 as r2 RUN P | destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 13)%Z (kk + 13)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c1_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 13) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps BSEGS (mkst regs (0xa1e2c : word) (MK kk) rom)
                   (mkst regs' (0xa1f4c : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    (first [ pose proof ((bits_lt32 (n - kk) ltac:(lia))) as dR_2; dand6 dR_2 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1bec : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1e2c D_a1e2c.                        (* [comment removed for export] *)
          renm. stepn F_a1e30 D_a1e30.                        (* [comment removed for export] *)
          renm. stepb_tk F_a1e34 D_a1e34 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_11; dand5 dR_11 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dex1 dR_3 as r2; destruct dR_3 as [RUN P] | pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dand3 dR_3 as r2 RUN P | destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1e38 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1e2c D_a1e2c.
          renm. stepn F_a1e30 D_a1e30.
          renm. stepb_ft F_a1e34 D_a1e34 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_12; dand5 dR_12 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1ec4 : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * (first [ pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as r2; destruct dR_4 as [RUN P] | pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dand3 dR_4 as r2 RUN P | destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_13; dand5 dR_13 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dex1 dR_5 as r3; destruct dR_5 as [RUN P] | pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dand3 dR_5 as r3 RUN P | destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c1_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps BSEGS (mkst regs (0xa1c00 : word) (MK k) rom)
                   (mkst regs' (0xa1f4c : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 1 <= n - (k + 3) < 16 * (Z.of_nat q + 1) + 17)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 3 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    (first [ pose proof ((bits_lt32 m ltac:(lia))) as dR_6; dand6 dR_6 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    (first [ pose proof ((c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dex1 dR_7 as r1; dand8 dR_7 as RUN1 P1 P11 P13 P12 P14 P15 K1 | pose proof ((c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dand9 dR_7 as r1 RUN1 P1 P11 P13 P12 P14 P15 K1 | destruct (c1_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1) ]).
    (first [ pose proof ((c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dex1 dR_8 as r2; dand6 dR_8 as RUN2 Q1 Q11 Q13 Q12 K2 | pose proof ((c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dand7 dR_8 as r2 RUN2 Q1 Q11 Q13 Q12 K2 | destruct (c1_loop q r1 ret (k + 3)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2) ]).
    fold kk in RUN2, Q11, Q13, Q12.
    (first [ pose proof ((c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dex1 dR_9 as r3; dand6 dR_9 as RUN3 S1 S11 S13 S12 K3 | pose proof ((c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dand7 dR_9 as r3 RUN3 S1 S11 S13 S12 K3 | destruct (c1_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3) ]).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Bothe0z.

Module Both5nv.
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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk WalkTac MmapSim RefMocc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothaek OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothpwm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothz8e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothh6z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Local Ltac stn_K := constr:(8%nat).
Local Ltac stn_depth R := lazymatch R with regupd ?R' _ _ => let d := stn_depth R' in constr:(S d) | _ => constr:(O) end.
Local Ltac stn_innermost m := lazymatch m with wbytes ?m' _ _ => lazymatch m' with wbytes _ _ _ => stn_innermost m' | _ => m end end.
Local Ltac stn_set t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_mark x).
Local Ltac stn_grow_fact x :=
  let body := eval unfold x in x in
  lazymatch body with wbytes ?p ?a ?bs =>
    let H := fresh "HMG" in
    first [ match goal with Hp : mem_grows ?b0 p |- _ => assert (H : mem_grows b0 x) by (exact (mem_grows_trans b0 p x Hp (wbytes_grows bs p a))) end
          | assert (H : mem_grows p x) by (exact (wbytes_grows bs p a)) ]
  end.
Local Ltac stn_setm t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_markm x); try stn_grow_fact x.
Local Ltac stn_name_regs R :=
  let d := stn_depth R in let k := stn_K in
  lazymatch eval cbv in (Nat.leb k d) with true => stn_set R ident:(RN) | false => idtac end.
Local Ltac stn_name_M :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ ?M _) _ =>
    lazymatch M with wbytes _ _ _ => idtac end;
    let t := stn_innermost M in stn_setm t ident:(MN) end).
(* [comment removed for export] *)
Local Ltac stn_eexists :=
  lazymatch goal with
  | |- @ex (bvmap _ _) _ => eapply stn_ex_by_eq; (let x := fresh "regsW" in let E := fresh "EregsW" in intros x E; pose proof (I : stn_mark E))
  | |- _ => eexists
  end.
Local Ltac stn_wit :=
  repeat match goal with
  | M : stn_mark ?E |- ?g => lazymatch type of E with ?x = _ => lazymatch g with context [x] => rewrite E end end
  end.
Local Ltac stn_begin :=
  lazymatch goal with
  | |- msteps _ _ ?t => tryif is_var t then idtac else (apply stn_msteps_tgt; let s := fresh "stF" in let E := fresh "EstF" in intros s E)
  | |- _ => idtac
  end.
Local Ltac renm :=
  stn_begin;
  lazymatch goal with
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
Local Ltac stn_done :=
  repeat first [ match goal with H : stn_mark ?x |- ?g => lazymatch g with context [x] => unfold x end end
               | match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end ];
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end;
  stn_wit.
Local Ltac stn_demand1 :=
  match goal with
  | M : stn_mark ?E |- context [getr ?x _] => lazymatch type of E with x = _ => rewrite E end
  | H : getr ?b ?x = _ |- context [getr ?b ?x] => is_var b; (let body := eval unfold b in b in idtac); rewrite !H
  | |- context [getr ?b ?x] =>
      is_var b;
      let body := eval unfold b in b in
      lazymatch body with regupd _ _ _ => idtac end;
      let l := gresl_list body in
      let bb := gresl_base body in
      let v := gresl_val body x in
      let H := fresh "HGN" in
      assert (H : getr b x = v) by (exact (getr_regupds l bb x (@eq_refl bool false)));
      rewrite !H
  end.
Local Ltac stn_gres_old :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let l := gresl_list X in
             let b := gresl_base X in
             let v := gresl_val X r in
             let p := constr:(getr_regupds l b r (@eq_refl bool false) : getr X r = v) in
             rewrite p
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac.gres ::= stn_gres_old; repeat (stn_demand1; stn_gres_old).
Local Ltac stn_sok_old :=
  lazymatch goal with
  | |- store_ok ?segs ?M ?a ?n = true =>
      let b := sokl_base M in
      lazymatch b with
      | M => idtac
      | _ => let l := sokl_list M in
             refine ((store_ok_layers segs n l b a _) : store_ok segs M a n = true)
      end
  | |- _ => idtac
  end.
Local Ltac stn_sok_named :=
  lazymatch goal with |- store_ok ?segs ?M ?a ?n = true =>
    is_var M; match goal with H : mem_grows ?b M |- _ => apply (store_ok_mono segs n b M a H) end end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.store_ok_peel ::= stn_sok_old; try stn_sok_named.

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Section C2.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac m16 := eapply (merge_s16 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma c2_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1c00 : word) (MK k) rom) (mkst regs' (0xa1c30 : word) (MK (k + 2)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 2)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 2)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 17 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. stn_eexists. split.
    - renm. mlw F_a1c00 D_a1c00 k.                            (* [comment removed for export] *)
      renm. stepn F_a1c04 D_a1c04.                            (* [comment removed for export] *)
      renm. stepb_ft F_a1c08 D_a1c08 ltac:(cond).             (* [comment removed for export] *)
      renm. stepn F_a1c0c D_a1c0c.                            (* [comment removed for export] *)
      renm. stepb_ft F_a1c10 D_a1c10 ltac:(cond).             (* [comment removed for export] *)
      renm. stepn F_a1c14 D_a1c14.                            (* [comment removed for export] *)
      renm. stepn F_a1c18 D_a1c18.                            (* [comment removed for export] *)
      renm. msb F_a1c1c D_a1c1c k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      renm. msb F_a1c20 D_a1c20 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
      renm. stepn F_a1c24 D_a1c24.                            (* [comment removed for export] *)
      renm. stepn F_a1c28 D_a1c28.                            (* [comment removed for export] *)
      renm. stepn F_a1c2c D_a1c2c.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post. stn_open. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c2_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 17 ->
    (ja = kk + 14)%Z -> (jw = kk - 2)%Z -> (2 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 2 <= n - kk < 16 * (Z.of_nat q + 1) + 18)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1c30 : word) (MK kk) rom)
                   (mkst regs' (0xa1c90 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 14)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - stn_eexists. split.
      + renm. stepn F_a1c30 D_a1c30.                          (* [comment removed for export] *)
        renm. mlw F_a1c34 D_a1c34 (kk + 2)%Z.                 (* [comment removed for export] *)
        renm. mlw F_a1c38 D_a1c38 (kk + 6)%Z.                 (* [comment removed for export] *)
        renm. mlw F_a1c3c D_a1c3c (kk + 10)%Z.                (* [comment removed for export] *)
        renm. mlw F_a1c40 D_a1c40 (kk + 14)%Z.                (* [comment removed for export] *)
        renm. stepn F_a1c44 D_a1c44. renm. stepn F_a1c48 D_a1c48. renm. stepn F_a1c4c D_a1c4c.   (* [comment removed for export] *)
        renm. stepn F_a1c50 D_a1c50. renm. stepn F_a1c54 D_a1c54. renm. stepn F_a1c58 D_a1c58.   (* [comment removed for export] *)
        renm. stepn F_a1c5c D_a1c5c. renm. stepn F_a1c60 D_a1c60. renm. stepn F_a1c64 D_a1c64.   (* [comment removed for export] *)
        renm. stepn F_a1c68 D_a1c68. renm. stepn F_a1c6c D_a1c6c.                          (* [comment removed for export] *)
        renm. stepn F_a1c70 D_a1c70.                          (* [comment removed for export] *)
        renm. msw F_a1c74 D_a1c74 kk ltac:(m16).              (* [comment removed for export] *)
        renm. msw F_a1c78 D_a1c78 (kk + 4)%Z ltac:(m16).      (* [comment removed for export] *)
        renm. msw F_a1c7c D_a1c7c (kk + 8)%Z ltac:(m16).      (* [comment removed for export] *)
        renm. msw F_a1c80 D_a1c80 (kk + 12)%Z ltac:(m16).     (* [comment removed for export] *)
        renm. stepn F_a1c84 D_a1c84.                          (* [comment removed for export] *)
        renm. stepn F_a1c88 D_a1c88.                          (* [comment removed for export] *)
        renm. stepb_ft F_a1c8c D_a1c8c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + post. stn_open. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1c30 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
                         /\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1c30 D_a1c30.
          renm. mlw F_a1c34 D_a1c34 (kk + 2)%Z.
          renm. mlw F_a1c38 D_a1c38 (kk + 6)%Z.
          renm. mlw F_a1c3c D_a1c3c (kk + 10)%Z.
          renm. mlw F_a1c40 D_a1c40 (kk + 14)%Z.
          renm. stepn F_a1c44 D_a1c44. renm. stepn F_a1c48 D_a1c48. renm. stepn F_a1c4c D_a1c4c.
          renm. stepn F_a1c50 D_a1c50. renm. stepn F_a1c54 D_a1c54. renm. stepn F_a1c58 D_a1c58.
          renm. stepn F_a1c5c D_a1c5c. renm. stepn F_a1c60 D_a1c60. renm. stepn F_a1c64 D_a1c64.
          renm. stepn F_a1c68 D_a1c68. renm. stepn F_a1c6c D_a1c6c.
          renm. stepn F_a1c70 D_a1c70.
          renm. msw F_a1c74 D_a1c74 kk ltac:(m16).
          renm. msw F_a1c78 D_a1c78 (kk + 4)%Z ltac:(m16).
          renm. msw F_a1c7c D_a1c7c (kk + 8)%Z ltac:(m16).
          renm. msw F_a1c80 D_a1c80 (kk + 12)%Z ltac:(m16).
          renm. stepn F_a1c84 D_a1c84.
          renm. stepn F_a1c88 D_a1c88.
          renm. stepb_tk F_a1c8c D_a1c8c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          stn_done. mk_eq. stn_done. apply mst_refl.
        * cbv beta. post. stn_open. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. (intros r1; (first [ intro dR_10; dand7 dR_10 as R1 R11 R13 R12 R14 R15 K1 | intros (R1 & R11 & R13 & R12 & R14 & R15 & K1) ])).
        (first [ pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; destruct dR_1 as [RUN P] | pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dand3 dR_1 as r2 RUN P | destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c2_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 14) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps BSEGS (mkst regs (0xa1c90 : word) (MK kk) rom)
                   (mkst regs' (0xa1f4c : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    (first [ pose proof ((bits_lt32 (n - kk) ltac:(lia))) as dR_2; dand6 dR_2 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1bec : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1c90 D_a1c90.                        (* [comment removed for export] *)
          renm. stepn F_a1c94 D_a1c94.                        (* [comment removed for export] *)
          renm. stepb_tk F_a1c98 D_a1c98 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_11; dand5 dR_11 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dex1 dR_3 as r2; destruct dR_3 as [RUN P] | pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dand3 dR_3 as r2 RUN P | destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1e38 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1c90 D_a1c90.
          renm. stepn F_a1c94 D_a1c94.
          renm. stepb_ft F_a1c98 D_a1c98 ltac:(cond).         (* [comment removed for export] *)
          renm. stepn F_a1c9c D_a1c9c.                        (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_12; dand5 dR_12 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1ec4 : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * (first [ pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as r2; destruct dR_4 as [RUN P] | pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dand3 dR_4 as r2 RUN P | destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_13; dand5 dR_13 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dex1 dR_5 as r3; destruct dR_5 as [RUN P] | pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dand3 dR_5 as r3 RUN P | destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c2_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 2 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps BSEGS (mkst regs (0xa1c00 : word) (MK k) rom)
                   (mkst regs' (0xa1f4c : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    (first [ pose proof ((bits_lt32 m ltac:(lia))) as dR_6; dand6 dR_6 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    (first [ pose proof ((c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dex1 dR_7 as r1; dand8 dR_7 as RUN1 P1 P11 P13 P12 P14 P15 K1 | pose proof ((c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dand9 dR_7 as r1 RUN1 P1 P11 P13 P12 P14 P15 K1 | destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1) ]).
    (first [ pose proof ((c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dex1 dR_8 as r2; dand6 dR_8 as RUN2 Q1 Q11 Q13 Q12 K2 | pose proof ((c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dand7 dR_8 as r2 RUN2 Q1 Q11 Q13 Q12 K2 | destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2) ]).
    fold kk in RUN2, Q11, Q13, Q12.
    (first [ pose proof ((c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dex1 dR_9 as r3; dand6 dR_9 as RUN3 S1 S11 S13 S12 K3 | pose proof ((c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dand7 dR_9 as r3 RUN3 S1 S11 S13 S12 K3 | destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3) ]).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Both5nv.

Module Both49i.
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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk WalkTac MmapSim RefMocc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothaek OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothpwm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothz8e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothh6z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stn_mark {A : Type} (x : A) : Prop := True.
Definition stn_markm {A : Type} (x : A) : Prop := True.      (* [comment removed for export] *)
Lemma stn_ex_by_eq : forall (A : Type) (P : A -> Prop) (w : A), (forall x, x = w -> P x) -> exists x, P x.
Proof. intros A P w H. exists w. exact (H w eq_refl). Qed.
Lemma stn_msteps_tgt : forall segs st tgt, (forall stF, stF = tgt -> msteps segs st stF) -> msteps segs st tgt.
Proof. intros segs st tgt H. exact (H tgt eq_refl). Qed.
Local Ltac stn_K := constr:(8%nat).
Local Ltac stn_depth R := lazymatch R with regupd ?R' _ _ => let d := stn_depth R' in constr:(S d) | _ => constr:(O) end.
Local Ltac stn_innermost m := lazymatch m with wbytes ?m' _ _ => lazymatch m' with wbytes _ _ _ => stn_innermost m' | _ => m end end.
Local Ltac stn_set t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_mark x).
Local Ltac stn_grow_fact x :=
  let body := eval unfold x in x in
  lazymatch body with wbytes ?p ?a ?bs =>
    let H := fresh "HMG" in
    first [ match goal with Hp : mem_grows ?b0 p |- _ => assert (H : mem_grows b0 x) by (exact (mem_grows_trans b0 p x Hp (wbytes_grows bs p a))) end
          | assert (H : mem_grows p x) by (exact (wbytes_grows bs p a)) ]
  end.
Local Ltac stn_setm t base :=
  let x := fresh base in set (x := t); pose proof (I : stn_markm x); try stn_grow_fact x.
Local Ltac stn_name_regs R :=
  let d := stn_depth R in let k := stn_K in
  lazymatch eval cbv in (Nat.leb k d) with true => stn_set R ident:(RN) | false => idtac end.
Local Ltac stn_name_M :=
  repeat (lazymatch goal with |- msteps _ (mkst _ _ ?M _) _ =>
    lazymatch M with wbytes _ _ _ => idtac end;
    let t := stn_innermost M in stn_setm t ident:(MN) end).
(* [comment removed for export] *)
Local Ltac stn_eexists :=
  lazymatch goal with
  | |- @ex (bvmap _ _) _ => eapply stn_ex_by_eq; (let x := fresh "regsW" in let E := fresh "EregsW" in intros x E; pose proof (I : stn_mark E))
  | |- _ => eexists
  end.
Local Ltac stn_wit :=
  repeat match goal with
  | M : stn_mark ?E |- ?g => lazymatch type of E with ?x = _ => lazymatch g with context [x] => rewrite E end end
  end.
Local Ltac stn_begin :=
  lazymatch goal with
  | |- msteps _ _ ?t => tryif is_var t then idtac else (apply stn_msteps_tgt; let s := fresh "stF" in let E := fresh "EstF" in intros s E)
  | |- _ => idtac
  end.
Local Ltac renm :=
  stn_begin;
  lazymatch goal with
  | |- msteps _ (mkst ?R _ _ _) _ => stn_name_regs R; stn_name_M
  | |- _ => idtac
  end.
Local Ltac stn_open := repeat match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end.
Local Ltac stn_done :=
  repeat first [ match goal with H : stn_mark ?x |- ?g => lazymatch g with context [x] => unfold x end end
               | match goal with H : stn_markm ?x |- ?g => lazymatch g with context [x] => unfold x end end ];
  try lazymatch goal with E : ?s = _ |- msteps _ _ ?s => rewrite E end;
  stn_wit.
Local Ltac stn_demand1 :=
  match goal with
  | M : stn_mark ?E |- context [getr ?x _] => lazymatch type of E with x = _ => rewrite E end
  | H : getr ?b ?x = _ |- context [getr ?b ?x] => is_var b; (let body := eval unfold b in b in idtac); rewrite !H
  | |- context [getr ?b ?x] =>
      is_var b;
      let body := eval unfold b in b in
      lazymatch body with regupd _ _ _ => idtac end;
      let l := gresl_list body in
      let bb := gresl_base body in
      let v := gresl_val body x in
      let H := fresh "HGN" in
      assert (H : getr b x = v) by (exact (getr_regupds l bb x (@eq_refl bool false)));
      rewrite !H
  end.
Local Ltac stn_gres_old :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let l := gresl_list X in
             let b := gresl_base X in
             let v := gresl_val X r in
             let p := constr:(getr_regupds l b r (@eq_refl bool false) : getr X r = v) in
             rewrite p
         end;
  match goal with |- context [getr _ 0] => rewrite ?getr_zero | _ => idtac end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac.gres ::= stn_gres_old; repeat (stn_demand1; stn_gres_old).
Local Ltac stn_sok_old :=
  lazymatch goal with
  | |- store_ok ?segs ?M ?a ?n = true =>
      let b := sokl_base M in
      lazymatch b with
      | M => idtac
      | _ => let l := sokl_list M in
             refine ((store_ok_layers segs n l b a _) : store_ok segs M a n = true)
      end
  | |- _ => idtac
  end.
Local Ltac stn_sok_named :=
  lazymatch goal with |- store_ok ?segs ?M ?a ?n = true =>
    is_var M; match goal with H : mem_grows ?b M |- _ => apply (store_ok_mono segs n b M a H) end end.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk.store_ok_peel ::= stn_sok_old; try stn_sok_named.

Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps ::=
  stn_wit; repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.solve_keeps_cs ::=
  stn_wit;
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
(* [comment removed for export] *)
Section C3.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac m8 := eapply (merge_s8 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  Lemma c3_pro : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1c00 : word) (MK k) rom) (mkst regs' (0xa1d38 : word) (MK (k + 1)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (k + 16) /\ getr regs' 13 = at_ dst (k + 1)
      /\ getr regs' 12 = Z_to_bv 64 (n - (k + 1)) /\ getr regs' 14 = LWv (SB k 4)
      /\ getr regs' 15 = Z_to_bv 64 18 /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. stn_eexists. split.
    - renm. mlw F_a1c00 D_a1c00 k.                            (* [comment removed for export] *)
      renm. stepn F_a1c04 D_a1c04.                            (* [comment removed for export] *)
      renm. stepb_tk F_a1c08 D_a1c08 ltac:(cond).             (* [comment removed for export] *)
      renm. msb F_a1d24 D_a1d24 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      renm. stepn F_a1d28 D_a1d28.                            (* [comment removed for export] *)
      renm. stepn F_a1d2c D_a1d2c.                            (* [comment removed for export] *)
      renm. stepn F_a1d30 D_a1d30.                            (* [comment removed for export] *)
      renm. stepn F_a1d34 D_a1d34.                            (* [comment removed for export] *)
      stn_done. mk_eq. stn_done. apply mst_refl.
    - post. stn_open. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma c3_loop : forall (q : nat) regs (ret : word) kk ja jw,
    getr regs 1 = ret -> getr regs 11 = at_ src ja -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) -> getr regs 14 = LWv (SB jw 4) -> getr regs 15 = Z_to_bv 64 18 ->
    (ja = kk + 15)%Z -> (jw = kk - 1)%Z -> (1 <= kk)%Z ->
    (16 * (Z.of_nat q + 1) + 3 <= n - kk < 16 * (Z.of_nat q + 1) + 19)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1d38 : word) (MK kk) rom)
                   (mkst regs' (0xa1d98 : word) (MK (kk + 16 * (Z.of_nat q + 1))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + 16 * (Z.of_nat q + 1) + 15)
      /\ getr regs' 13 = at_ dst (kk + 16 * (Z.of_nat q + 1))
      /\ getr regs' 12 = Z_to_bv 64 (n - (kk + 16 * (Z.of_nat q + 1))) /\ keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - stn_eexists. split.
      + renm. stepn F_a1d38 D_a1d38.                          (* [comment removed for export] *)
        renm. mlw F_a1d3c D_a1d3c (kk + 3)%Z.                 (* [comment removed for export] *)
        renm. mlw F_a1d40 D_a1d40 (kk + 7)%Z.                 (* [comment removed for export] *)
        renm. mlw F_a1d44 D_a1d44 (kk + 11)%Z.                (* [comment removed for export] *)
        renm. mlw F_a1d48 D_a1d48 (kk + 15)%Z.                (* [comment removed for export] *)
        renm. stepn F_a1d4c D_a1d4c. renm. stepn F_a1d50 D_a1d50. renm. stepn F_a1d54 D_a1d54.
        renm. stepn F_a1d58 D_a1d58. renm. stepn F_a1d5c D_a1d5c. renm. stepn F_a1d60 D_a1d60.
        renm. stepn F_a1d64 D_a1d64. renm. stepn F_a1d68 D_a1d68. renm. stepn F_a1d6c D_a1d6c.
        renm. stepn F_a1d70 D_a1d70. renm. stepn F_a1d74 D_a1d74.
        renm. stepn F_a1d78 D_a1d78.                          (* [comment removed for export] *)
        renm. msw F_a1d7c D_a1d7c kk ltac:(m8).
        renm. msw F_a1d80 D_a1d80 (kk + 4)%Z ltac:(m8).
        renm. msw F_a1d84 D_a1d84 (kk + 8)%Z ltac:(m8).
        renm. msw F_a1d88 D_a1d88 (kk + 12)%Z ltac:(m8).
        renm. stepn F_a1d8c D_a1d8c.                          (* [comment removed for export] *)
        renm. stepn F_a1d90 D_a1d90.                          (* [comment removed for export] *)
        renm. stepb_ft F_a1d94 D_a1d94 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        stn_done. mk_eq. stn_done. apply mst_refl.
      + post. stn_open. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1d38 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 15) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 15) 4)
                         /\ getr r 15 = Z_to_bv 64 18 /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1d38 D_a1d38.
          renm. mlw F_a1d3c D_a1d3c (kk + 3)%Z.
          renm. mlw F_a1d40 D_a1d40 (kk + 7)%Z.
          renm. mlw F_a1d44 D_a1d44 (kk + 11)%Z.
          renm. mlw F_a1d48 D_a1d48 (kk + 15)%Z.
          renm. stepn F_a1d4c D_a1d4c. renm. stepn F_a1d50 D_a1d50. renm. stepn F_a1d54 D_a1d54.
          renm. stepn F_a1d58 D_a1d58. renm. stepn F_a1d5c D_a1d5c. renm. stepn F_a1d60 D_a1d60.
          renm. stepn F_a1d64 D_a1d64. renm. stepn F_a1d68 D_a1d68. renm. stepn F_a1d6c D_a1d6c.
          renm. stepn F_a1d70 D_a1d70. renm. stepn F_a1d74 D_a1d74.
          renm. stepn F_a1d78 D_a1d78.
          renm. msw F_a1d7c D_a1d7c kk ltac:(m8).
          renm. msw F_a1d80 D_a1d80 (kk + 4)%Z ltac:(m8).
          renm. msw F_a1d84 D_a1d84 (kk + 8)%Z ltac:(m8).
          renm. msw F_a1d88 D_a1d88 (kk + 12)%Z ltac:(m8).
          renm. stepn F_a1d8c D_a1d8c.
          renm. stepn F_a1d90 D_a1d90.
          renm. stepb_tk F_a1d94 D_a1d94 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          stn_done. mk_eq. stn_done. apply mst_refl.
        * cbv beta. post. stn_open. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. (intros r1; (first [ intro dR_10; dand7 dR_10 as R1 R11 R13 R12 R14 R15 K1 | intros (R1 & R11 & R13 & R12 & R14 & R15 & K1) ])).
        (first [ pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dex1 dR_1 as r2; destruct dR_1 as [RUN P] | pose proof ((IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_1; dand3 dR_1 as r2 RUN P | destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma c3_exit : forall regs (ret : word) kk,
    getr regs 1 = ret -> getr regs 11 = at_ src (kk + 15) -> getr regs 13 = at_ dst kk ->
    getr regs 12 = Z_to_bv 64 (n - kk) ->
    (0 <= kk)%Z -> (n - kk < 32)%Z -> (kk <= n)%Z ->
    let m := (n - kk)%Z in
    exists regs',
      msteps BSEGS (mkst regs (0xa1d98 : word) (MK kk) rom)
                   (mkst regs' (0xa1f4c : word) (MK (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 13 = at_ dst (kk + Z.land m 16 + Z.land m 8 + Z.land m 4)
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    (first [ pose proof ((bits_lt32 (n - kk) ltac:(lia))) as dR_2; dand6 dR_2 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1bec : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1d98 D_a1d98.                        (* [comment removed for export] *)
          renm. stepn F_a1d9c D_a1d9c.                        (* [comment removed for export] *)
          renm. stepb_tk F_a1da0 D_a1da0 ltac:(cond).         (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_11; dand5 dR_11 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dex1 dR_3 as r2; destruct dR_3 as [RUN P] | pose proof ((t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia))) as dR_3; dand3 dR_3 as r2 RUN P | destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P) ]).
        exists r2. stn_open. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1e38 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + stn_eexists. split.
        * renm. stepn F_a1d98 D_a1d98.
          renm. stepn F_a1d9c D_a1d9c.
          renm. stepb_ft F_a1da0 D_a1da0 ltac:(cond).
          renm. stepn F_a1da4 D_a1da4.                        (* [comment removed for export] *)
          stn_done. apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_12; dand5 dR_12 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1ec4 : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * (first [ pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as r2; destruct dR_4 as [RUN P] | pose proof ((b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia))) as dR_4; dand3 dR_4 as r2 RUN P | destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_13; dand5 dR_13 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dex1 dR_5 as r3; destruct dR_5 as [RUN P] | pose proof ((b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia))) as dR_5; dand3 dR_5 as r3 RUN P | destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P) ]).
          exists r3. stn_open. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  Lemma c3_run : forall regs (ret : word) k,
    getr regs 1 = ret -> getr regs 11 = at_ src k -> getr regs 13 = at_ dst k ->
    getr regs 12 = Z_to_bv 64 (n - k) -> getr regs 15 = Z_to_bv 64 3 ->
    (0 <= k)%Z -> (32 <= n - k)%Z ->
    exists regs' m,
      msteps BSEGS (mkst regs (0xa1c00 : word) (MK k) rom)
                   (mkst regs' (0xa1f4c : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
      /\ (0 <= m < 32)%Z
      /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
      /\ getr regs' 12 = Z_to_bv 64 m /\ keeps regs regs'.
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 3 <= n - (k + 1) < 16 * (Z.of_nat q + 1) + 19)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 1 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    (first [ pose proof ((bits_lt32 m ltac:(lia))) as dR_6; dand6 dR_6 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    (first [ pose proof ((c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dex1 dR_7 as r1; dand8 dR_7 as RUN1 P1 P11 P13 P12 P14 P15 K1 | pose proof ((c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk)) as dR_7; dand9 dR_7 as r1 RUN1 P1 P11 P13 P12 P14 P15 K1 | destruct (c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1) ]).
    (first [ pose proof ((c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dex1 dR_8 as r2; dand6 dR_8 as RUN2 Q1 Q11 Q13 Q12 K2 | pose proof ((c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)) as dR_8; dand7 dR_8 as r2 RUN2 Q1 Q11 Q13 Q12 K2 | destruct (c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2) ]).
    fold kk in RUN2, Q11, Q13, Q12.
    (first [ pose proof ((c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dex1 dR_9 as r3; dand6 dR_9 as RUN3 S1 S11 S13 S12 K3 | pose proof ((c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_9; dand7 dR_9 as r3 RUN3 S1 S11 S13 S12 K3 | destruct (c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3) ]).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Both49i.

Module Both068.
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

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StepTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk WalkTac MmapSim RefMocc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.WalkTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothaek OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothpwm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothz8e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothe0z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Both5nv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Both49i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothh6z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac chkp_cleanup :=
  repeat
    (repeat match goal with
       | [ H : (0 <= ?x < _)%Z |- _ ] =>
          destruct H;
          try (lazymatch type of H with (* [comment removed for export] *)
            | (0 <= x < _)%Z => clear H (* [comment removed for export] *)
          end)
          (* [comment removed for export] *)
       end;
     repeat match goal with
       | [ H : (?x <> ?x)%Z -> _ |- _ ] => clear H
       | [ H : (?x < ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?T -> _, H' : ~?T |- _ ] => clear H
       | [ H : ~?T -> _, H' : ?T |- _ ] => clear H
       | [ H : ?A -> (?x <> ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?A -> (?x < ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?A -> ?B -> _, H' : ~?B |- _ ] => clear H
       | [ H : ?A -> ~?B -> _, H' : ?B |- _ ] => clear H
       | [ H : (0 < ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : (?x < 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 < ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x < 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : (0 <= ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : (?x <= 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 <= ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x <= 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : (0 < ?x)%Z -> _, H' : (?x <= 0)%Z |- _ ] => clear H
       | [ H : (?x < 0)%Z -> _, H' : (0 <= ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 < ?x)%Z -> _, H' : (?x <= 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x < 0)%Z -> _, H' : (0 <= ?x)%Z |- _ ] => clear H
       | [ H : (?x < ?y)%Z -> _, H' : ?x = ?y |- _ ] => clear H
       | [ H : (?x < ?y)%Z -> _, H' : ?y = ?x |- _ ] => clear H
       | [ H : ?A -> (?x < ?y)%Z -> _, H' : ?x = ?y |- _ ] => clear H
       | [ H : ?A -> (?x < ?y)%Z -> _, H' : ?y = ?x |- _ ] => clear H
       | [ H : ?x = ?y -> _, H' : (?x < ?y)%Z |- _ ] => clear H
       | [ H : ?x = ?y -> _, H' : (?y < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> ?x = ?y -> _, H' : (?x < ?y)%Z |- _ ] => clear H
       | [ H : ?A -> ?x = ?y -> _, H' : (?y < ?x)%Z |- _ ] => clear H
       end;
     repeat match goal with
       | [ H : ?x = ?x -> ?Q |- _ ] => specialize (H eq_refl)
       | [ H : ?T -> ?Q, H' : ?T |- _ ] => specialize (H H')
       | [ H : ?A -> ?x = ?x -> ?Q |- _ ] => specialize (fun a => H a eq_refl)
       | [ H : ?A -> ?B -> ?Q, H' : ?B |- _ ] => specialize (fun a => H a H')
       | [ H : (0 <= ?x)%Z -> ?Q, H' : (?x <= 0)%Z |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x (eq_sym pf)))
       | [ H : ?A -> (0 <= ?x)%Z -> ?Q, H' : (?x <= 0)%Z |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl 0 x (eq_sym pf)))
       | [ H : (?x <= 0)%Z -> ?Q, H' : (0 <= ?x)%Z |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x pf))
       | [ H : ?A -> (?x <= 0)%Z -> ?Q, H' : (0 <= ?x)%Z |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl x 0 pf))
       end).
Local Ltac nia := Zify.zify; chkp_cleanup; xnia zchecker.
Local Ltac liac := Zify.zify; chkp_cleanup; xlia zchecker.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ALL.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  (* [comment removed for export] *)
  Ltac conda := rwH; unfold at_; cond.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_finish : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1cac : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 H12 Hk.
    set (m := ((n - k) mod 16)%Z).
    pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)) as Hm16.
    (first [ pose proof ((bits_lt32 m ltac:(lia))) as dR_1; dand6 dR_1 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    assert (Hl16 : Z.land m 16 = 0%Z) by (destruct B16 as [E|E]; [exact E|exfalso; lia]).
    eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1ce8 : word) (MK (n - m)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { (first [ pose proof ((al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk)) as dR_2; dex1 dR_2 as r; destruct dR_2 as [R P] | pose proof ((al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk)) as dR_2; dand3 dR_2 as r R P | destruct (al16_run _ _ _ _ _ rom HOK regs ret k H1 H11 H13 H12 Hk) as (r & R & P) ]). exists r.
      subst m. split; [exact R|]. decompose [and] P. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. }
    cbv beta. (intros r2; (first [ intro dR_21; dand5 dR_21 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
    eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1d08 : word) (MK (n - m + Z.land m 8)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { (first [ pose proof ((al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_3; dex1 dR_3 as r; destruct dR_3 as [R P] | pose proof ((al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_3; dand3 dR_3 as r R P | destruct (al8_run _ _ _ _ _ rom HOK r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P) ]).
      exists r. split; [exact R|]. decompose [and] P. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. (intros r3; (first [ intro dR_22; dand5 dR_22 as T1 T11 T13 T12 K3 | intros (T1 & T11 & T13 & T12 & K3) ])).
    eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1f4c : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { (first [ pose proof ((al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_4; dex1 dR_4 as r; destruct dR_4 as [R P] | pose proof ((al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_4; dand3 dR_4 as r R P | destruct (al4_run _ _ _ _ _ rom HOK r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r & R & P) ]).
      exists r. split; [exact R|]. decompose [and] P. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. (intros r4; (first [ intro dR_23; dand5 dR_23 as U1 U11 U13 U12 K4 | intros (U1 & U11 & U13 & U12 & K4) ])).
    (first [ pose proof ((t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_5; dex1 dR_5 as r; destruct dR_5 as [R P] | pose proof ((t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_5; dand3 dR_5 as r R P | destruct (t2_run _ _ _ _ _ rom HOK r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r & R & P) ]).
    exists r. split; [exact R | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mis_run : forall regs (ret : word) k q,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 15 = Z_to_bv 64 q -> (q = 1 \/ q = 2 \/ q = 3)%Z ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1bdc : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k q Hret H1 H11 H13 H12 H15 Hq Hk.
    destruct (Z.lt_ge_cases (n - k) 32) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      (first [ pose proof ((bits_lt32 (n - k) ltac:(lia))) as dR_6; dand6 dR_6 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 (n - k) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
      assert (0 <= Z.land (n - k) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 4)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 1)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 16)%Z by (apply Z.land_nonneg; lia).
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1be4 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + eexists. split.
        * stepn F_a1bdc D_a1bdc.                        (* [comment removed for export] *)
          stepb_ft F_a1be0 D_a1be0 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_24; dand5 dR_24 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        set (m := (n - k)%Z) in *.
        eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1f4c : word) (MK (k + Z.land m 16 + Z.land m 8 + Z.land m 4)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
                           /\ getr r 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * (first [ pose proof ((t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_7; dex1 dR_7 as r2; destruct dR_7 as [RUN P] | pose proof ((t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia))) as dR_7; dand3 dR_7 as r2 RUN P | destruct (t16_run _ _ _ _ _ rom HOK r1 ret k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P) ]).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2; (first [ intro dR_25; dand5 dR_25 as S1 S11 S13 S12 K2 | intros (S1 & S11 & S13 & S12 & K2) ])).
          (first [ pose proof ((t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
                      ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_8; dex1 dR_8 as r3; destruct dR_8 as [RUN K3] | pose proof ((t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
                      ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_8; dand3 dR_8 as r3 RUN K3 | destruct (t2_run _ _ _ _ _ rom HOK r2 ret (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
                      ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN & K3) ]).
          exists r3. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1c00 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + eexists. split.
        * stepn F_a1bdc D_a1bdc.                        (* [comment removed for export] *)
          stepb_tk F_a1be0 D_a1be0 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_26; dand6 dR_26 as R1 R11 R13 R12 R15 K1 | intros (R1 & R11 & R13 & R12 & R15 & K1) ])).
        assert (CASE : exists regs' m,
          msteps BSEGS (mkst r1 (0xa1c00 : word) (MK k) rom)
                       (mkst regs' (0xa1f4c : word) (MK (n - (Z.land m 2 + Z.land m 1))) rom)
          /\ (0 <= m < 32)%Z
          /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 12 = Z_to_bv 64 m /\ keeps r1 regs').
        { destruct Hq as [-> | [-> | ->]].
          - apply (c1_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
          - apply (c2_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia.
          - apply (c3_run _ _ _ _ _ rom HOK r1 ret k); try assumption; lia. }
        (first [ dex2 CASE as r2 m; dand7 CASE as RUN Hm S1 S11 S13 S12 K2 | dand9 CASE as r2 m RUN Hm S1 S11 S13 S12 K2 | destruct CASE as (r2 & m & RUN & Hm & S1 & S11 & S13 & S12 & K2) ]).
        (first [ pose proof ((bits_lt32 m Hm)) as dR_10; dand6 dR_10 as B16 B8 B4 B2 B1 Bsum | destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum) ]).
        assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
        (first [ pose proof ((t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
                    ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_11; dex1 dR_11 as r3; destruct dR_11 as [RUN3 K3] | pose proof ((t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
                    ltac:(lia) B2 B1 ltac:(lia) ltac:(lia))) as dR_11; dand3 dR_11 as r3 RUN3 K3 | destruct (t2_run _ _ _ _ _ rom HOK r2 ret (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
                    ltac:(lia) B2 B1 ltac:(lia) ltac:(lia)) as (r3 & RUN3 & K3) ]).
        exists r3. split; [eapply msteps_trans; [exact RUN | exact RUN3] |].
        eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma j_run : forall regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1bd4 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret k Hret H1 H11 H13 H12 Hk.
    pose proof (u64_range dst).
    set (q := ((bv_unsigned dst + k) mod 4)%Z).
    pose proof (Z.mod_pos_bound (bv_unsigned dst + k) 4 ltac:(lia)) as Hq4.
    destruct (Z.eq_dec q 0) as [Hq0|Hq0].
    - (* [comment removed for export] *)
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1cac : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + eexists. split.
        * stepn F_a1bd4 D_a1bd4.                        (* [comment removed for export] *)
          stepb_tk F_a1bd8 D_a1bd8 ltac:(conda).        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1; (first [ intro dR_27; dand5 dR_27 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
        (first [ pose proof ((al_finish r1 ret k Hret R1 R11 R13 R12 Hk)) as dR_12; dex1 dR_12 as r2; destruct dR_12 as [RUN K2] | pose proof ((al_finish r1 ret k Hret R1 R11 R13 R12 Hk)) as dR_12; dand3 dR_12 as r2 RUN K2 | destruct (al_finish r1 ret k Hret R1 R11 R13 R12 Hk) as (r2 & RUN & K2) ]).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1bdc : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + eexists. split.
        * stepn F_a1bd4 D_a1bd4.
          stepb_ft F_a1bd8 D_a1bd8 ltac:(conda).        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post. unfold v_andi, at_. subst q. rewrite <- land_3 by lia. unorm.
          change (bv_wrap 64 3) with 3%Z. reflexivity.
      + cbv beta. (intros r1; (first [ intro dR_28; dand6 dR_28 as R1 R11 R13 R12 R15 K1 | intros (R1 & R11 & R13 & R12 & R15 & K1) ])).
        (first [ pose proof ((mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk)) as dR_13; dex1 dR_13 as r2; destruct dR_13 as [RUN K2] | pose proof ((mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk)) as dR_13; dand3 dR_13 as r2 RUN K2 | destruct (mis_run r1 ret k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk) as (r2 & RUN & K2) ]).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma hl_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = at_ src (k + 1) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (k < n)%Z -> ((bv_unsigned src + k) mod 4 <> 0)%Z ->
    (Z.of_nat i + 1 = Z.min (n - k) (4 - (bv_unsigned src + k) mod 4))%Z ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1ba4 : word) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ keeps regs regs'.
  Proof.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 H14 H15 Hk Hkn Hal Hi.
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      destruct (Z.eq_dec ((bv_unsigned src + (k + 1)) mod 4) 0) as [Hz|Hz].
      + eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1bd4 : word) (MK (k + 1)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * eexists. split.
          -- mlbu F_a1ba4 D_a1ba4 k.                    (* [comment removed for export] *)
             stepn F_a1ba8 D_a1ba8.                    (* [comment removed for export] *)
             stepn F_a1bac D_a1bac.                    (* [comment removed for export] *)
             stepn F_a1bb0 D_a1bb0.                    (* [comment removed for export] *)
             msb F_a1bb4 D_a1bb4 k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
             stepn F_a1bb8 D_a1bb8.                    (* [comment removed for export] *)
             stepn F_a1bbc D_a1bbc.                    (* [comment removed for export] *)
             stepb_tk F_a1bc0 D_a1bc0 ltac:(conda).    (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
        * cbv beta. (intros r1; (first [ intro dR_29; dand5 dR_29 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
          (first [ pose proof ((j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia))) as dR_14; dex1 dR_14 as r2; destruct dR_14 as [RUN K2] | pose proof ((j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia))) as dR_14; dand3 dR_14 as r2 RUN K2 | destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2) ]).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1bd4 : word) (MK (k + 1)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * eexists. split.
          -- mlbu F_a1ba4 D_a1ba4 k.
             stepn F_a1ba8 D_a1ba8.
             stepn F_a1bac D_a1bac.
             stepn F_a1bb0 D_a1bb0.
             msb F_a1bb4 D_a1bb4 k ltac:(apply sb_val_plain).
             stepn F_a1bb8 D_a1bb8.
             stepn F_a1bbc D_a1bbc.
             stepb_ft F_a1bc0 D_a1bc0 ltac:(conda).    (* [comment removed for export] *)
             stepn F_a1bc4 D_a1bc4.                    (* [comment removed for export] *)
             stepb_ft F_a1bc8 D_a1bc8 ltac:(cond).     (* [comment removed for export] *)
             stepn F_a1bcc D_a1bcc.                    (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
        * cbv beta. (intros r1; (first [ intro dR_30; dand5 dR_30 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
          (first [ pose proof ((j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia))) as dR_15; dex1 dR_15 as r2; destruct dR_15 as [RUN K2] | pose proof ((j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia))) as dR_15; dand3 dR_15 as r2 RUN K2 | destruct (j_run r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2) ]).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1ba4 : word) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                         /\ getr r 14 = at_ src (k + 1 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
      + eexists. split.
        * mlbu F_a1ba4 D_a1ba4 k.
          stepn F_a1ba8 D_a1ba8.
          stepn F_a1bac D_a1bac.
          stepn F_a1bb0 D_a1bb0.
          msb F_a1bb4 D_a1bb4 k ltac:(apply sb_val_plain).
          stepn F_a1bb8 D_a1bb8.
          stepn F_a1bbc D_a1bbc.
          stepb_ft F_a1bc0 D_a1bc0 ltac:(conda).       (* [comment removed for export] *)
          stepn F_a1bc4 D_a1bc4.                       (* [comment removed for export] *)
          stepb_tk F_a1bc8 D_a1bc8 ltac:(cond).        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. (intros r1; (first [ intro dR_31; dand7 dR_31 as R1 R11 R13 R12 R14 R15 K1 | intros (R1 & R11 & R13 & R12 & R14 & R15 & K1) ])).
        (first [ pose proof ((IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_16; dex1 dR_16 as r2; destruct dR_16 as [RUN K2] | pose proof ((IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as dR_16; dand3 dR_16 as r2 RUN K2 | destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & K2) ]).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem ref_memcpy : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps BSEGS (mkst regs (0xa1b8c : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src). pose proof (u64_range dst).
    rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
    assert (H11' : getr regs 11 = at_ src 0) by (rewrite at_0; exact H11).
    assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
    destruct (Z.eq_dec (bv_unsigned src mod 4) 0) as [Hs4|Hs4].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (bv_unsigned dst mod 4) 0) as [Hd4|Hd4].
      + eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1cac : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * eexists. split.
          -- stepn F_a1b8c D_a1b8c.                     (* [comment removed for export] *)
             stepb_tk F_a1b90 D_a1b90 ltac:(conda).     (* [comment removed for export] *)
             stepn F_a1ca0 D_a1ca0.                     (* [comment removed for export] *)
             stepn F_a1ca4 D_a1ca4.                     (* [comment removed for export] *)
             stepb_ft F_a1ca8 D_a1ca8 ltac:(cond).      (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. (intros r1; (first [ intro dR_32; dand5 dR_32 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
          (first [ pose proof ((al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia))) as dR_17; dex1 dR_17 as r2; destruct dR_17 as [RUN K2] | pose proof ((al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia))) as dR_17; dand3 dR_17 as r2 RUN K2 | destruct (al_finish r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2) ]).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1bdc : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 15 = Z_to_bv 64 (bv_unsigned dst mod 4) /\ keeps regs r)).
        * eexists. split.
          -- stepn F_a1b8c D_a1b8c.
             stepb_tk F_a1b90 D_a1b90 ltac:(conda).
             stepn F_a1ca0 D_a1ca0.
             stepn F_a1ca4 D_a1ca4.
             stepb_tk F_a1ca8 D_a1ca8 ltac:(cond).      (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post; try (rewrite at_0; reflexivity).
             unfold v_andi. rewrite <- land_3 by lia. change (bv_wrap 64 3) with 3%Z. reflexivity.
        * cbv beta. (intros r1; (first [ intro dR_33; dand6 dR_33 as R1 R11 R13 R12 R15 K1 | intros (R1 & R11 & R13 & R12 & R15 & K1) ])).
          pose proof (Z.mod_pos_bound (bv_unsigned dst) 4 ltac:(lia)).
          (first [ pose proof ((mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia))) as dR_18; dex1 dR_18 as r2; destruct dR_18 as [RUN K2] | pose proof ((mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia))) as dR_18; dand3 dR_18 as r2 RUN K2 | destruct (mis_run r1 ret 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2) ]).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hn0z|Hn0z].
      + eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1bd4 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * eexists. split.
          -- stepn F_a1b8c D_a1b8c.                     (* [comment removed for export] *)
             stepb_ft F_a1b90 D_a1b90 ltac:(conda).     (* [comment removed for export] *)
             stepb_tk F_a1b94 D_a1b94 ltac:(cond).      (* [comment removed for export] *)
             stepn F_a1bd0 D_a1bd0.                     (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. (intros r1; (first [ intro dR_34; dand5 dR_34 as R1 R11 R13 R12 K1 | intros (R1 & R11 & R13 & R12 & K1) ])).
          (first [ pose proof ((j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia))) as dR_19; dex1 dR_19 as r2; destruct dR_19 as [RUN K2] | pose proof ((j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia))) as dR_19; dand3 dR_19 as r2 RUN K2 | destruct (j_run r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia)) as (r2 & RUN & K2) ]).
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
      + set (i := Z.to_nat (Z.min n (4 - bv_unsigned src mod 4) - 1)).
        pose proof (Z.mod_pos_bound (bv_unsigned src) 4 ltac:(lia)).
        eapply (runs_trans BSEGS _ (fun r => mkst r (0xa1ba4 : word) (MK 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 14 = at_ src (0 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
        * eexists. split.
          -- stepn F_a1b8c D_a1b8c.                     (* [comment removed for export] *)
             stepb_ft F_a1b90 D_a1b90 ltac:(conda).     (* [comment removed for export] *)
             stepb_ft F_a1b94 D_a1b94 ltac:(cond).      (* [comment removed for export] *)
             stepn F_a1b98 D_a1b98.                     (* [comment removed for export] *)
             stepn F_a1b9c D_a1b9c.                     (* [comment removed for export] *)
             stepn F_a1ba0 D_a1ba0.                     (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. (intros r1; (first [ intro dR_35; dand7 dR_35 as R1 R11 R13 R12 R14 R15 K1 | intros (R1 & R11 & R13 & R12 & R14 & R15 & K1) ])).
          (first [ pose proof ((hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4))) as dR_20; dex1 dR_20 as r2; destruct dR_20 as [RUN K2] | pose proof ((hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4))) as dR_20; dand3 dR_20 as r2 RUN K2 | destruct (hl_loop i r1 ret 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4)) as (r2 & RUN & K2) ]).
          { subst i. rewrite Z.add_0_r, Z.sub_0_r. rewrite Z2Nat.id; lia. }
          exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.

End ALL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Both068.

Module Sumsxiz.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require RefMocc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.RefMocc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SumsLib Bothp5b.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SumsLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothp5b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothv4r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothhsz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Memsalo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Both2uj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan18z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z.Asan59m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

#[local] Notation BSEGS := AsanUbsan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kept_ok_of_regs_agree : forall (clob : list reg) regs regs',
  (forall r, In r clob -> In (AX2.ridx r) APC.caller_saved) ->
  regs_agree (fun r => In r clob) regs regs' -> APSX.kept_ok regs regs'.
Proof. intros clob regs regs' Hsub Hag r Hr0 Hnin. apply Hag. intros Hin. apply Hnin. apply Hsub. exact Hin. Qed.

#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).

#[local] Ltac clob_sub :=
  let r := fresh "r" in let H := fresh "H" in
  intros r H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [in_list|]); destruct H.

Lemma imemset_clob_sub : forall r, In r imemset_clob -> In (AX2.ridx r) APC.caller_saved.
Proof. unfold imemset_clob. clob_sub. Qed.
Lemma imemcpy_clob_sub : forall r, In r imemcpy_clob -> In (AX2.ridx r) APC.caller_saved.
Proof. unfold imemcpy_clob. clob_sub. Qed.
Lemma memisz_clob_sub : forall r, In r memisz_clob -> In (AX2.ridx r) APC.caller_saved.
Proof. unfold memisz_clob. clob_sub. Qed.
Lemma ms_clob_sub : forall r, In r ms_clob -> In (AX2.ridx r) APC.caller_saved.
Proof. unfold ms_clob. clob_sub. Qed.

(* [comment removed for export] *)
Lemma kept_ok_of_keeps : forall regs regs', keeps regs regs' -> APSX.kept_ok regs regs'.
Proof.
  intros regs regs' Hk r Hr0 Hnin. apply Hk.
  pose proof (AX2S.ridx_range r) as Hrr.
  assert (Hr : AX2.ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (APSX.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
  unfold APC.caller_saved in Hnin. cbn [In] in Hnin.
  assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
  { exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
  destruct E as (k & Hink & Hrk). rewrite (APSX.reg_of_ridx r k Hrk).
  cbn [In] in Hink. unfold callee_kept.
  repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma segs_wr_of_forallb : forall segs,
  forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool segs = true -> APSX.segs_wr_ok segs.
Proof.
  intros segs H seg Hin Hw. pose proof (proj1 (forallb_forall _ _) H seg Hin) as Hs. cbn beta in Hs.
  rewrite Hw in Hs. exact Hs.
Qed.

Lemma both_segs_wr : APSX.segs_wr_ok BSEGS.
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Derive.
Variable SEGS : list Segment.

(* [comment removed for export] *)
Lemma fill_spec_of_imemset : forall (entryw : word) (entry : Z),
  Z_to_bv 64 entry = entryw ->
  (forall mem0 (s c : word) n rom regs (ret : word),
    (0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
    store_ok SEGS mem0 s (Z.to_nat n) = true ->
    (align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = s -> getr regs 11%bv = c -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs entryw mem0 rom)
                  (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
      /\ regs_agree (fun r => In r imemset_clob) regs regs') ->
  APSX.fill_spec SEGS entry 256.
Proof.
  intros entryw entry He SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
  destruct (SUM mem0 s c n (seg_rom SEGS) regs ret Hn Hnw Hst ltac:(intros; exact Hc) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
  exists regs'. rewrite He. split; [exact Hms|]. split.
  - eapply kept_ok_of_regs_agree; [apply imemset_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold imemset_clob. cbn. intros [H|[H|[H|[]]]]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma fill_spec_of_memset : forall (entry : Z),
  (forall mem0 (d cv ret : word) (n : Z) rom,
    (0 <= n)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z ->
    store_ok SEGS mem0 d (Z.to_nat n) = true -> ret_ok ret ->
    forall regs, getr regs 10%bv = d -> getr regs 11%bv = cv -> getr regs 12%bv = Z_to_bv 64 n -> getr regs 1%bv = ret ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 rom)
                  (mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
      /\ getr regs' 10%bv = d /\ ms_agree regs regs') ->
  APSX.fill_spec SEGS entry AX2.two64.
Proof.
  intros entry SUM mem0 s c n regs ret Hn Hnw Hst Hc Hret R1 R10 R11 R12.
  destruct (SUM mem0 s c ret n (seg_rom SEGS) Hn Hnw Hst Hret regs R10 R11 R12 R1) as (regs' & Hms & H10 & Hag).
  exists regs'. split; [exact Hms|]. split; [|exact H10].
  eapply kept_ok_of_regs_agree; [apply ms_clob_sub | exact Hag].
Qed.

(* [comment removed for export] *)
Lemma copy_spec_of_imemcpy : forall (entryw : word) (entry : Z),
  Z_to_bv 64 entry = entryw ->
  (forall mem0 (dst src : word) n bs rom regs (ret : word),
    cpyH SEGS mem0 dst src n bs ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs entryw mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ regs_agree (fun r => In r imemcpy_clob) regs regs') ->
  APSX.copy_spec SEGS entry.
Proof.
  intros entryw entry He SUM mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  destruct (SUM mem0 dst src n bs (seg_rom SEGS) regs ret ltac:(constructor; assumption) Hret R1 R10 R11 R12) as (regs' & Hms & Hag).
  exists regs'. rewrite He. split; [exact Hms|]. split.
  - eapply kept_ok_of_regs_agree; [apply imemcpy_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold imemcpy_clob. cbn. intros [H|[H|[H|[H|[]]]]]; discriminate.
Qed.

(* [comment removed for export] *)
Lemma miz_spec_of_summary : forall (entryw : word) (entry : Z),
  Z_to_bv 64 entry = entryw ->
  (forall mem (beg sp : word) N rom regs (ret : word),
    (0 <= N <= 2 ^ 40)%Z ->
    (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z ->
    (16 <= bv_unsigned sp)%Z ->
    store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
    (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z ->
    (forall a : word, (bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N)%Z ->
       rdn SEGS mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp ->
    getr regs 10%bv = beg -> getr regs 11%bv = Z_to_bv 64 N ->
    exists regs',
      msteps SEGS (mkst regs entryw mem rom)
                  (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) rom)
      /\ regs_agree (fun r => In r memisz_clob) regs regs'
      /\ getr regs' 10%bv = Z_to_bv 64 1 /\ getr regs' 2%bv = sp /\ getr regs' 1%bv = ret) ->
  APSX.miz_spec SEGS entry.
Proof.
  intros entryw entry He SUM mem beg sp N regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11.
  destruct (SUM mem beg sp N (seg_rom SEGS) regs ret HN Hnw Hsp Hst Hdisj Hz Hret R1 R2 R10 R11) as (regs' & Hms & Hag & H10 & _ & _).
  exists regs'. rewrite He. split; [exact Hms|]. split; [|exact H10].
  eapply kept_ok_of_regs_agree; [apply memisz_clob_sub | exact Hag].
Qed.
End Derive.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma both_fill_spec_imemset : APSX.fill_spec BSEGS (APC.x_imemset BOTH) 256.
Proof.
  apply (fill_spec_of_imemset _ both_imemset_entry); [apply bv_eq; reflexivity|].
  exact both_imemset.
Qed.

Lemma both_fill_spec_memset : APSX.fill_spec BSEGS (APC.x_memset BOTH) AX2.two64.
Proof.
  apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
  exact (Bothtil.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.

Lemma both_copy_spec_imemcpy : APSX.copy_spec BSEGS (APC.x_imemcpy BOTH).
Proof.
  apply (copy_spec_of_imemcpy _ both_imemcpy_entry); [apply bv_eq; reflexivity|].
  exact both_imemcpy.
Qed.

Lemma both_copy_spec_memcpy : APSX.copy_spec BSEGS (APC.x_memcpy BOTH).
Proof.
  intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  pose proof (u64_range dst) as Hdr.
  assert (HOK : Bothaek.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
  destruct (Both068.ref_memcpy mem0 dst src n bs (seg_rom BSEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
  exists regs'. split; [replace (Z_to_bv 64 (APC.x_memcpy BOTH)) with (0xa1b8c%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
  split; [apply kept_ok_of_keeps; exact Hk|].
  rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

Lemma both_miz_spec : APSX.miz_spec BSEGS (APC.x_memiszero BOTH).
Proof.
  apply (miz_spec_of_summary _ both_mem_is_zero_entry); [apply bv_eq; reflexivity|].
  exact both_mem_is_zero.
Qed.

End Sumsxiz.

Module BSumhgd.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6a59c : bv 32 := 0x06060663.
Lemma D_6a59c : decode_any W_6a59c = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5a0 : bv 32 := 0x00000693.
Lemma D_6a5a0 : decode_any W_6a5a0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5a4 : bv 32 := 0x00d58733.
Lemma D_6a5a4 : decode_any W_6a5a4 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5a8 : bv 32 := 0x00074703.
Lemma D_6a5a8 : decode_any W_6a5a8 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5ac : bv 32 := 0x00070c63.
Lemma D_6a5ac : decode_any W_6a5ac = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5b0 : bv 32 := 0x00d507b3.
Lemma D_6a5b0 : decode_any W_6a5b0 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5b4 : bv 32 := 0x00168693.
Lemma D_6a5b4 : decode_any W_6a5b4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5b8 : bv 32 := 0x00e78023.
Lemma D_6a5b8 : decode_any W_6a5b8 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5bc : bv 32 := 0xfed614e3.
Lemma D_6a5bc : decode_any W_6a5bc = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5c0 : bv 32 := 0x00060693.

(* [comment removed for export] *)
Definition W_6a5c4 : bv 32 := 0x00d505b3.
Lemma D_6a5c4 : decode_any W_6a5c4 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5c8 : bv 32 := 0x40d6073b.
Lemma D_6a5c8 : decode_any W_6a5c8 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5cc : bv 32 := 0x00b76733.
Lemma D_6a5cc : decode_any W_6a5cc = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5d0 : bv 32 := 0x00f77713.
Lemma D_6a5d0 : decode_any W_6a5d0 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5d4 : bv 32 := 0x00070e63.
Lemma D_6a5d4 : decode_any W_6a5d4 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5d8 : bv 32 := 0x02d60863.
Lemma D_6a5d8 : decode_any W_6a5d8 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5dc : bv 32 := 0x00c50633.
Lemma D_6a5dc : decode_any W_6a5dc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5e0 : bv 32 := 0x00058023.
Lemma D_6a5e0 : decode_any W_6a5e0 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5e4 : bv 32 := 0x00158593.
Lemma D_6a5e4 : decode_any W_6a5e4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5e8 : bv 32 := 0xfec59ce3.
Lemma D_6a5e8 : decode_any W_6a5e8 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5ec : bv 32 := 0x01c0006f.
Lemma D_6a5ec : decode_any W_6a5ec = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6a5f0 : bv 32 := 0x00d60c63.

(* [comment removed for export] *)
Definition W_6a5f4 : bv 32 := 0x00c50633.

(* [comment removed for export] *)
Definition W_6a5f8 : bv 32 := 0x0005b023.

(* [comment removed for export] *)
Definition W_6a5fc : bv 32 := 0x0005b423.

(* [comment removed for export] *)
Definition W_6a600 : bv 32 := 0x01058593.

(* [comment removed for export] *)
Definition W_6a604 : bv 32 := 0xfec5eae3.

(* [comment removed for export] *)
Definition W_6a608 : bv 32 := 0x00008067.
Lemma D_6a608 : decode_any W_6a608 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End BSumhgd.

Module Both3xh.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require SumsLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothp5b.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SumsLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.BSumhgd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothp5b.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition istrncpy_words : list (bv 32) :=
  [W_6a59c; W_6a5a0; W_6a5a4; W_6a5a8; W_6a5ac; W_6a5b0; W_6a5b4; W_6a5b8;
   W_6a5bc; W_6a5c0; W_6a5c4; W_6a5c8; W_6a5cc; W_6a5d0; W_6a5d4; W_6a5d8;
   W_6a5dc; W_6a5e0; W_6a5e4; W_6a5e8; W_6a5ec; W_6a5f0; W_6a5f4; W_6a5f8;
   W_6a5fc; W_6a600; W_6a604; W_6a608].

(* [comment removed for export] *)
Definition istrncpy_clob : list reg := [11; 12; 13; 14; 15].

(* [comment removed for export] *)
Definition sealed8 : list byte :=
  [Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e].
Definition strncpy_sealed_bytes : list byte := sealed8 ++ zeros 4087.

(* [comment removed for export] *)

Lemma sealed8_nz : forall j, (0 <= j < 8)%Z -> bv_unsigned (b_ sealed8 j) <> 0%Z.
Proof.
  intros j Hj.
  assert (E : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7)%Z) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst j; cbv; discriminate.
Qed.

(* [comment removed for export] *)
Lemma align15_4087 : forall d : word, align15 4087 d <> 0%Z.
Proof.
  intros d H. unfold align15 in H. rewrite Z.land_lor_distr_l in H.
  apply Z.lor_eq_0_iff in H as [H _]. cbv in H. discriminate.
Qed.

Section ISTRNCPY.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 istrncpy_words.
  (* [comment removed for export] *)
  Hypothesis Hsrc : rdn segs mem0 src 8%nat = Some sealed8.
  Hypothesis Hnul : rdn segs mem0 (at_ src 8) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis Hsnw : (bv_unsigned src + 9 < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis Hok : store_ok segs mem0 dst 4095%nat = true.
  Hypothesis Hnw : (bv_unsigned dst + 4095 < 2 ^ 64)%Z.
  Hypothesis Hdisj : (bv_unsigned dst + 4095 <= bv_unsigned src \/ bv_unsigned src + 9 <= bv_unsigned dst)%Z.

  #[local] Abbreviation CL := (fun r => In r istrncpy_clob).

  (* [comment removed for export] *)
  Ltac condv :=
    rwH; rewrite ?at_addi; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; unorm; lia.

  (* [comment removed for export] *)
  Lemma HMC : cpyH segs mem0 dst src 8 sealed8.
  Proof.
    pose proof (u64_range dst). pose proof (u64_range src).
    apply CPYH.
    - lia.
    - reflexivity.
    - exact Hsrc.
    - cbn [length]. eapply (store_ok_sub segs mem0 dst dst 4095%nat 8%nat); [lia | exact Hok | lia | cbn; lia].
    - lia.
    - lia.
    - lia.
  Qed.

  #[local] Abbreviation MK := (memk mem0 dst sealed8).
  (* [comment removed for export] *)
  Definition MZ (k : Z) : word -> option byte := msetk (MK 8) (at_ dst 8) (Z_to_bv 8 0) k.

  (* [comment removed for export] *)

  Lemma MZ_final : MZ 4087 = wbytes mem0 dst strncpy_sealed_bytes.
  Proof.
    unfold MZ, msetk, strncpy_sealed_bytes, zeros. rewrite (memk_n _ _ _ _ _ _ HMC).
    rewrite wbytes_app. reflexivity.
  Qed.

  Lemma MK8_ok : store_ok segs (MK 8) (at_ dst 8) (Z.to_nat 4087) = true.
  Proof.
    unfold memk. pose proof (u64_range dst).
    apply (store_ok_at segs mem0 dst 4095%nat); [lia | exact Hok | lia | cbn; lia].
  Qed.

  Lemma at8_nw : (bv_unsigned (at_ dst 8) + 4087 < 2 ^ 64)%Z.
  Proof. pose proof (u64_range dst). rewrite at_u by lia. lia. Qed.

  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at istrncpy_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60
                    & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & _).

  (* [comment removed for export] *)
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HMC) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (memk _ _ _ ?a) _) _ =>
                     first [constr_eq a kk | replace (memk mem0 dst sealed8 a) with (memk mem0 dst sealed8 kk) by (f_equal; lia)] end.
  Ltac msb F D kk :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HMC) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia
        | gres; rwH; reflexivity | apply sb_val_b | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Ltac mz_at kk := match goal with |- msteps _ (mkst _ _ (MZ ?a) _) _ =>
                     first [constr_eq a kk | replace (MZ a) with (MZ kk) by (f_equal; lia)] end.
  Ltac mzsb F D kk :=
    mz_at kk; unfold MZ;
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := at_ (at_ dst 8) kk) (v := Z_to_bv 64 0) (b := Z_to_bv 8 0);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi, ?at_at; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity | reflexivity
        | apply (wr_s segs (MK 8) (at_ dst 8) 4087 (Z_to_bv 8 0) ltac:(lia) at8_nw MK8_ok); cbn; lia ]
      | step_simpl];
    rewrite (msetk_extend1 (MK 8) (at_ dst 8) (Z_to_bv 8 0) kk) by lia; fold (MZ (kk + 1)); vn.

  (* [comment removed for export] *)
  Lemma fill_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ dst (8 + k) -> getr regs 12 = at_ dst 4095 ->
    (0 <= k)%Z -> (8 + k < 4095)%Z -> (Z.of_nat i = 4095 - 8 - k - 1)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 68) (MZ k) rom) (mkst regs' ret (MZ 4087) rom)
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. pose proof (u64_range dst) as Hd.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H12 Hk Hkn Hi.
    - eexists. split.
      + mzsb C68 D_6a5e0 k.                                (* [comment removed for export] *)
        an C72 D_6a5e4.                                    (* [comment removed for export] *)
        ab_ft C76 D_6a5e8 ltac:(condz).                    (* [comment removed for export] *)
        an C80 D_6a5ec.                                    (* [comment removed for export] *)
        aret C108 D_6a608 ret.
        mz_at 4087%Z. apply mst_refl.
      + unfold istrncpy_clob. solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + (k + 1)) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
      + eexists. split.
        * mzsb C68 D_6a5e0 k.
          an C72 D_6a5e4.
          ab_tk C76 D_6a5e8 ltac:(condz).                  (* [comment removed for export] *)
          mz_at (k + 1)%Z. apply mst_refl.
        * post. unfold istrncpy_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R12 & AG).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma copy_iter : forall regs (j : Z),
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 4095 ->
    getr regs 13 = Z_to_bv 64 j -> (0 <= j < 8)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 8) (MK j) rom) (mkst regs' (at_ base 8) (MK (j + 1)) rom)
      /\ getr regs' 10 = dst /\ getr regs' 11 = src /\ getr regs' 12 = Z_to_bv 64 4095
      /\ getr regs' 13 = Z_to_bv 64 (j + 1) /\ regs_agree CL regs regs'.
  Proof.
    get_code. intros regs j H10 H11 H12 H13 Hj. pose proof (u64_range dst). pose proof (u64_range src).
    eexists. split.
    - av C8 D_6a5a4 (at_ src j) ltac:(apply v_add_at; lia).          (* [comment removed for export] *)
      mlbu C12 D_6a5a8 j.                                              (* [comment removed for export] *)
      ab_ft C16 D_6a5ac
        ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; pose proof (u8_range (b_ sealed8 j));
              rewrite (u_Z2bv (bv_unsigned (b_ sealed8 j))) by lia; rewrite (u_Z2bv 0) by lia;
              apply sealed8_nz; lia).                                  (* [comment removed for export] *)
      av C20 D_6a5b0 (at_ dst j) ltac:(apply v_add_at; lia).          (* [comment removed for export] *)
      an C24 D_6a5b4.                                                  (* [comment removed for export] *)
      msb C28 D_6a5b8 j.                                               (* [comment removed for export] *)
      ab_tk C32 D_6a5bc ltac:(condv).                                  (* [comment removed for export] *)
      mk_at (j + 1)%Z. apply mst_refl.
    - post; try (unfold istrncpy_clob; solve_regs_agree). unfold v_addi. unorm. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma copy8 : forall regs0 rr,
    regs_agree CL regs0 rr ->
    getr rr 10 = dst -> getr rr 11 = src -> getr rr 12 = Z_to_bv 64 4095 ->
    getr rr 13 = Z_to_bv 64 0 ->
    exists regs',
      msteps segs (mkst rr (at_ base 8) (MK 0) rom) (mkst regs' (at_ base 8) (MK 8) rom)
      /\ getr regs' 10 = dst /\ getr regs' 11 = src /\ getr regs' 12 = Z_to_bv 64 4095
      /\ getr regs' 13 = Z_to_bv 64 8 /\ regs_agree CL regs0 regs'.
  Proof.
    intros regs0 rr K A B C D.
    Ltac cp_iter :=
      match goal with
      | K : regs_agree _ ?regs0 ?rr, A : getr ?rr 10 = _, B : getr ?rr 11 = _, C : getr ?rr 12 = _, D : getr ?rr 13 = Z_to_bv 64 ?v |- _ =>
        let jj := eval vm_compute in v in
        let jj1 := eval vm_compute in (v + 1)%Z in
        change (Z_to_bv 64 v) with (Z_to_bv 64 jj) in D;
        try change (memk mem0 dst sealed8 v) with (memk mem0 dst sealed8 jj);
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK jj1) rom)
                 (fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
                           /\ getr r 13 = Z_to_bv 64 jj1 /\ regs_agree CL regs0 r));
        [ destruct (copy_iter rr jj A B C D ltac:(lia)) as (r' & RUN & B10 & B11 & B12 & B13 & K');
          exists r'; split; [exact RUN | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; eapply regs_agree_trans; [exact K | exact K']]
        | cbv beta; clear rr K A B C D; intros rr (A & B & C & D & K) ]
      end.
    do 8 cp_iter.
    exists rr. split; [apply mst_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption].
  Qed.

  Theorem istrncpy_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 4095 ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem0 rom)
                  (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs.
    rewrite <- MZ_final.
    change (mkst regs (at_ base 0) mem0 rom) with (mkst regs (at_ base 0) (MK 0) rom).
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK 0) rom)
             (fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
                       /\ getr r 13 = Z_to_bv 64 0 /\ regs_agree CL regs r)).
    { eexists. split.
      - ab_ft C0 D_6a59c ltac:(condz).                                  (* [comment removed for export] *)
        an C4 D_6a5a0.                                                   (* [comment removed for export] *)
        apply mst_refl.
      - post. unfold istrncpy_clob. solve_regs_agree. }
    cbv beta. intros r0 (A10 & A11 & A12 & A13 & K0).
    (* [comment removed for export] *)
    destruct (copy8 regs r0 K0 A10 A11 A12 A13) as (r8 & RUN8 & L10 & L11 & L12 & L13 & K8).
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK 8) rom)
             (fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
                       /\ getr r 13 = Z_to_bv 64 8 /\ regs_agree CL regs r)).
    { exists r8. split; [exact RUN8 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption]. }
    cbv beta. clear r8 RUN8 L10 L11 L12 L13 K8. intros r8 (L10 & L11 & L12 & L13 & K8).
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ 0) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + 0) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
    { eexists. split.
      - av C8 D_6a5a4 (at_ src 8) ltac:(apply v_add_at; lia).         (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lbu with (b := Z_to_bv 8 0);
            [exact C12 | reflexivity | exact D_6a5a8
            | gres; rwH; imm_norm; rewrite at_addi; replace (at_ src (8 + 0)) with (at_ src 8) by (f_equal; lia);
              unfold memk; change (firstn (Z.to_nat 8) sealed8) with sealed8;
              rewrite rdn_wbytes_out;
              [ exact Hnul
              | change (length sealed8) with 8%nat; rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
              | rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
              | change (length sealed8) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ] ]
          | step_simpl]; vn.                                             (* [comment removed for export] *)
        ab_tk C16 D_6a5ac ltac:(condz).                                (* [comment removed for export] *)
        change (memk mem0 dst sealed8 8) with (MZ 0).
        av C40 D_6a5c4 (at_ dst 8) ltac:(apply v_add_at; lia).          (* [comment removed for export] *)
        an C44 D_6a5c8.                                                  (* [comment removed for export] *)
        (* [comment removed for export] *)
        an C48 D_6a5cc.
        av C52 D_6a5d0 (Z_to_bv 64 (align15 4087 (at_ dst 8)))
           ltac:(rewrite <- (u_align15 4087 (at_ dst 8)) by lia; symmetry; apply Z_to_bv_bv_unsigned).
        pose proof (align15_4087 (at_ dst 8)) as HA. pose proof (align15_range 4087 (at_ dst 8) ltac:(lia)) as HAR.
        ab_ft C56 D_6a5d4 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; rewrite !u_Z2bv by lia; exact HA).
        ab_ft C60 D_6a5d8 ltac:(condz).                                 (* [comment removed for export] *)
        av C64 D_6a5dc (at_ dst 4095) ltac:(apply v_add_at; lia).       (* [comment removed for export] *)
        apply mst_refl.
      - post.
        + rewrite <- H1. apply K8. unfold istrncpy_clob. cbn. intros [X|[X|[X|[X|[X|[]]]]]]; discriminate.
        + unfold istrncpy_clob in *. ra_chain. }
    cbv beta. intros r9 (M1 & M11 & M12 & K9).
    destruct (fill_loop (Z.to_nat 4086) r9 ret 0 Hret M1 M11 M12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r10 & RUN & K10).
    exists r10. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End ISTRNCPY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition both_istrncpy_entry : word := 0x6a59c.
Definition both_sealed_src : Z := 0x118be.  (* [comment removed for export] *)

Lemma both_istrncpy_code :
  code_at AsanUbsan.M.loaded_segments both_istrncpy_entry 0 istrncpy_words.
Proof. unfold istrncpy_words. code_at_vm. Qed.

(* [comment removed for export] *)
Lemma both_sealed_src_img : forall mem,
  (forall i, (both_sealed_src <= i < both_sealed_src + 9)%Z -> mem (Z_to_bv 64 i) = None) ->
  rdn AsanUbsan.M.loaded_segments mem (Z_to_bv 64 both_sealed_src) 8 = Some sealed8
  /\ rdn AsanUbsan.M.loaded_segments mem (at_ (Z_to_bv 64 both_sealed_src) 8) 1 = Some [Z_to_bv 8 0].
Proof.
  intros mem Hnone. unfold both_sealed_src in *. split.
  - rewrite (rdn_ext _ 8 mem (fun _ => None)); [vm_compute; reflexivity | u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - rewrite (rdn_ext _ 1 mem (fun _ => None)); [vm_compute; reflexivity | rewrite at_u by (u_norm; lia); u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. rewrite at_u by (u_norm; lia). u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Theorem both_istrncpy_sealed : forall mem0 (dst : word) rom regs (ret : word),
  (forall i, (both_sealed_src <= i < both_sealed_src + 9)%Z -> mem0 (Z_to_bv 64 i) = None) ->
  store_ok AsanUbsan.M.loaded_segments mem0 dst 4095%nat = true ->
  (bv_unsigned dst + 4095 < 2 ^ 64)%Z ->
  (bv_unsigned dst + 4095 <= both_sealed_src \/ both_sealed_src + 9 <= bv_unsigned dst)%Z ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = Z_to_bv 64 both_sealed_src -> getr regs 12 = Z_to_bv 64 4095 ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs both_istrncpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
    /\ regs_agree (fun r => In r istrncpy_clob) regs regs'.
Proof.
  intros mem0 dst rom regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  destruct (both_sealed_src_img mem0 Hnone) as [Hs Hn].
  rewrite <- (at_0 both_istrncpy_entry).
  apply (istrncpy_run _ _ mem0 dst (Z_to_bv 64 both_sealed_src) rom both_istrncpy_code Hs Hn); try assumption;
    unfold both_sealed_src in *; u_norm; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Both3xh.

Module Asan4iy.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan18z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z.Asanvp3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

#[local] Notation BSEGS := AsanUbsan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
Definition both_popfree_head : Z := 0x3c510.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma PF0 : fetch_word BSEGS (Z_to_bv 64 both_popfree_head) = Some PW0. Proof. vm_refl. Qed.
Lemma PF1 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 4)) = Some PW1. Proof. vm_refl. Qed.
Lemma PF2 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 8)) = Some PW2. Proof. vm_refl. Qed.
Lemma PF3 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 12)) = Some PW3. Proof. vm_refl. Qed.
Lemma PF4 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 16)) = Some PW4. Proof. vm_refl. Qed.
Lemma PF5 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 20)) = Some PW5. Proof. vm_refl. Qed.
Lemma PF6 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 24)) = Some PW6. Proof. vm_refl. Qed.
Lemma PF7 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 28)) = Some PW7. Proof. vm_refl. Qed.

Theorem both_popfree_spec : popfree_spec AsanUbsan.M.loaded_segments both_popfree_head.
Proof.
  apply popfree_spec_of_code; [unfold both_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End Asan4iy.

Module Sums618.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan18z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan18z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothny9.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z.Asanvp3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z.Asan59m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Sumsxiz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Both3xh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Asan4iy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma istrncpy_clob_sub : forall r, In r istrncpy_clob -> In (AX2.ridx r) APC.caller_saved.
Proof.
  intros r H. unfold istrncpy_clob in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [cbn; tauto|]). destruct H.
Qed.

Lemma both_istrncpy_spec : APSX.istrncpy_spec BSEGS (APC.x_istrncpy BOTH) (APC.x_sealed BOTH).
Proof.
  intros mem0 dst regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12.
  destruct (both_istrncpy_sealed mem0 dst (seg_rom BSEGS) regs ret Hnone Hst Hnw Hdisj Hret R1 R10 R11 R12)
    as (regs' & Hms & Hag).
  exists regs'. split; [|split].
  - replace APSX.SEALED_BYTES with strncpy_sealed_bytes by reflexivity.
    replace (Z_to_bv 64 (APC.x_istrncpy BOTH)) with both_istrncpy_entry by (apply bv_eq; reflexivity). exact Hms.
  - eapply kept_ok_of_regs_agree; [apply istrncpy_clob_sub | exact Hag].
  - rewrite <- R10. apply Hag. unfold istrncpy_clob. cbn. intros [H|[H|[H|[H|[H|[]]]]]]; discriminate.
Qed.

Lemma both_popfree_spec' : popfree_spec BSEGS (APC.x_popfree BOTH).
Proof. exact both_popfree_spec. Qed.

(* [comment removed for export] *)

Section AsanNodes.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> APC.CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_ok : APS.nx0_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.

#[local] Notation XSTMT := (APS.x_stmt BSEGS BOTH nx0 LIMIT SINV argH FS0).

#[local] Ltac close_with NODE SPEC :=
  eapply NODE; try eassumption;
  first [ exact both_wx | exact both_in_hull | exact both_res_len | exact both_hull_ok | exact both_segs_wr | exact SPEC | idtac ].

Theorem both_node_x_sound_XIMemset : XSTMT AP.XIMemset.
Proof. eapply APSX.node_x_sound_XIMemset; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_fill_spec_imemset. Qed.
Theorem both_node_x_sound_XMemset : XSTMT AP.XMemset.
Proof. eapply APSX.node_x_sound_XMemset; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_fill_spec_memset. Qed.
Theorem both_node_x_sound_XIMemcpy : XSTMT AP.XIMemcpy.
Proof. eapply APSX.node_x_sound_XIMemcpy; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_copy_spec_imemcpy. Qed.
Theorem both_node_x_sound_XMemcpy : XSTMT AP.XMemcpy.
Proof. eapply APSX.node_x_sound_XMemcpy; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_copy_spec_memcpy. Qed.
Theorem both_node_x_sound_XMemIsZero : XSTMT AP.XMemIsZero.
Proof. eapply APSX.node_x_sound_XMemIsZero; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_miz_spec. Qed.
Theorem both_node_x_sound_XIStrncpy : XSTMT AP.XIStrncpy.
Proof. eapply APSX.node_x_sound_XIStrncpy; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_istrncpy_spec. Qed.
Theorem both_node_x_sound_XPopFree : XSTMT AP.XPopFree.
Proof. eapply APSX.node_x_sound_XPopFree; try eassumption; try apply both_segs_wr; try apply both_wx; try apply both_in_hull;
       try apply both_res_len; try apply both_hull_ok. apply both_popfree_spec'. Qed.
End AsanNodes.
End Sums618.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99.

Module Bothlqx.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_97990 : bv 32 := 0x0004b503.
Lemma F_97990 : fetch_word AsanUbsan.M.loaded_segments (0x97990 : word) = Some W_97990.
Proof. vm_refl. Qed.
Lemma D_97990 : decode_any W_97990 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97994 : bv 32 := 0x00848493.
Lemma F_97994 : fetch_word AsanUbsan.M.loaded_segments (0x97994 : word) = Some W_97994.
Proof. vm_refl. Qed.
Lemma D_97994 : decode_any W_97994 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97998 : bv 32 := 0xfe051ce3.
Lemma F_97998 : fetch_word AsanUbsan.M.loaded_segments (0x97998 : word) = Some W_97998.
Proof. vm_refl. Qed.
Lemma D_97998 : decode_any W_97998 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_97a4c : bv 32 := 0x00b53023.
Lemma F_97a4c : fetch_word AsanUbsan.M.loaded_segments (0x97a4c : word) = Some W_97a4c.
Proof. vm_refl. Qed.
Lemma D_97a4c : decode_any W_97a4c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97a50 : bv 32 := 0x00158593.
Lemma F_97a50 : fetch_word AsanUbsan.M.loaded_segments (0x97a50 : word) = Some W_97a50.
Proof. vm_refl. Qed.
Lemma D_97a50 : decode_any W_97a50 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97a54 : bv 32 := 0xfff5c683.
Lemma F_97a54 : fetch_word AsanUbsan.M.loaded_segments (0x97a54 : word) = Some W_97a54.
Proof. vm_refl. Qed.
Lemma D_97a54 : decode_any W_97a54 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97a58 : bv 32 := 0xfec68ae3.
Lemma F_97a58 : fetch_word AsanUbsan.M.loaded_segments (0x97a58 : word) = Some W_97a58.
Proof. vm_refl. Qed.
Lemma D_97a58 : decode_any W_97a58 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_97a5c : bv 32 := 0xfe069ae3.
Lemma F_97a5c : fetch_word AsanUbsan.M.loaded_segments (0x97a5c : word) = Some W_97a5c.
Proof. vm_refl. Qed.
Lemma D_97a5c : decode_any W_97a5c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
End Bothlqx.

Module Asanc52.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk ShapeAlg SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanoq0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanoq0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm AsanInit Bothny9.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanj99 Asanxvb.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99.Asanfjy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99.Asangat OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanxvb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Bothlqx.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.

  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  #[local] Notation SINV0i := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH0i := (argH0 BPH sp rdraw argv envp uid hw).

  Lemma sp_lo' : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi' : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.
  Lemma argH0_agree_n : forall E E' (a : word), env_agree nx0 E E' -> argH0i E a = argH0i E' a.
  Proof. reflexivity. Qed.
  Lemma nx0_ok_n : APS.nx0_ok nx0.
  Proof. unfold APS.nx0_ok. unfold NX0 in Hnx0. lia. Qed.

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0i E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0i E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt BSEGS BOTH nx0 (@AsanInit.blim BL) SINV argH0i FS0 XEnvScan.
    Proof.
      exact (x_sound_envscan BSEGS BOTH nx0 (@AsanInit.blim BL) SINV argH0i FS0 both_wx both_in_hull both_hull_ok SINV_frame
                W_97990 W_97994 W_97998
                ltac:(cbn [x_envscan x_envscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_97990) (fetch_lit _ _ _ _ eq_refl F_97994) (fetch_lit _ _ _ _ eq_refl F_97998)
                ltac:(repeat split; reflexivity)
                D_97990 D_97994 D_97998
                BPH sp rdraw argv envp uid hw Hva Hve sp_lo' sp_hi'
                (SINV0_vals BPH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit SINV SINV_SINV0)
                (SINV0_sp BPH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit SINV SINV_SINV0)
                (SINV0_envp BPH sp rdraw brk0 argv envp uid hw SINV SINV_SINV0)).
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt BSEGS BOTH nx0 (@AsanInit.blim BL) SINV argH0i FS0 XPnScan.
    Proof.
      exact (x_sound_pnscan BSEGS BOTH nx0 (@AsanInit.blim BL) SINV argH0i FS0 both_wx both_in_hull both_hull_ok
                (argH0_high BPH sp rdraw argv envp uid hw Hsp Hva) argH0_agree_n SINV_frame SINV_agree nx0_ok_n
                W_97a4c W_97a50 W_97a54 W_97a58 W_97a5c
                ltac:(cbn [x_pnscan x_pnscan_k BOTH]; lia)
                (fetch_lit _ _ _ _ eq_refl F_97a4c) (fetch_lit _ _ _ _ eq_refl F_97a50) (fetch_lit _ _ _ _ eq_refl F_97a54)
                (fetch_lit _ _ _ _ eq_refl F_97a58) (fetch_lit _ _ _ _ eq_refl F_97a5c)
                ltac:(repeat split; reflexivity)
                D_97a4c D_97a50 D_97a54 D_97a58 D_97a5c
                BPH sp rdraw argv envp uid hw Hva Hve sp_lo' sp_hi'
                (SINV0_vals BPH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit SINV SINV_SINV0)
                (SINV0_sp BPH sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit SINV SINV_SINV0)
                (SINV0_str0 BPH sp rdraw brk0 argv envp Hva Hve uid hw Hfit SINV SINV_SINV0 SINV_frame)).
    Qed.

    (* [comment removed for export] *)
  End AnySINV.

  (* [comment removed for export] *)
  Lemma SINV0_agree_n : forall E E' M, env_agree nx0 E E' -> SINV0i E M -> SINV0i E' M.
  Proof. intros E E' M H HS. exact (SINV0_agree BPH sp rdraw brk0 argv envp uid hw E E' M (env_agree_le NX0 nx0 E E' H Hnx0) HS). Qed.

  Theorem node_x_sound_XEnvScan_asan : x_stmt BSEGS BOTH nx0 (@AsanInit.blim BL) SINV0i argH0i FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; [auto | apply SINV0_frame]. Qed.

  Theorem node_x_sound_XPnScan_asan : x_stmt BSEGS BOTH nx0 (@AsanInit.blim BL) SINV0i argH0i FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen; [auto | apply SINV0_frame | apply SINV0_agree_n]. Qed.

  Theorem node_x_sound_XLayout_asan : x_stmt BSEGS BOTH nx0 (@AsanInit.blim BL) SINV0i argH0i FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
End Asanc52.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb Bothy0u.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan18z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan18z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan18z.

Module Both61h.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6b7b8 : bv 32 := 0x00155593.
Lemma F_6b7b8 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7b8) = Some W_6b7b8.
Proof. vm_refl. Qed.
Lemma D_6b7b8 : decode_any W_6b7b8 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b7d8 : is_ecall W_6b7b8 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7bc : bv 32 := 0x55555637.
Lemma F_6b7bc : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7bc) = Some W_6b7bc.
Proof. vm_refl. Qed.
Lemma D_6b7bc : decode_any W_6b7bc = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b7dc : is_ecall W_6b7bc = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7c0 : bv 32 := 0x333336b7.
Lemma F_6b7c0 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7c0) = Some W_6b7c0.
Proof. vm_refl. Qed.
Lemma D_6b7c0 : decode_any W_6b7c0 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b7e0 : is_ecall W_6b7c0 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7c4 : bv 32 := 0x0f0f1737.
Lemma F_6b7c4 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7c4) = Some W_6b7c4.
Proof. vm_refl. Qed.
Lemma D_6b7c4 : decode_any W_6b7c4 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b7e4 : is_ecall W_6b7c4 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7c8 : bv 32 := 0x010107b7.
Lemma F_6b7c8 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7c8) = Some W_6b7c8.
Proof. vm_refl. Qed.
Lemma D_6b7c8 : decode_any W_6b7c8 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b7e8 : is_ecall W_6b7c8 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7cc : bv 32 := 0x00b56533.
Lemma F_6b7cc : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7cc) = Some W_6b7cc.
Proof. vm_refl. Qed.
Lemma D_6b7cc : decode_any W_6b7cc = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b7ec : is_ecall W_6b7cc = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7d0 : bv 32 := 0x5556059b.
Lemma F_6b7d0 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7d0) = Some W_6b7d0.
Proof. vm_refl. Qed.
Lemma D_6b7d0 : decode_any W_6b7d0 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b7f0 : is_ecall W_6b7d0 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7d4 : bv 32 := 0x3336861b.
Lemma F_6b7d4 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7d4) = Some W_6b7d4.
Proof. vm_refl. Qed.
Lemma D_6b7d4 : decode_any W_6b7d4 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b7f4 : is_ecall W_6b7d4 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7d8 : bv 32 := 0xf0f7069b.
Lemma F_6b7d8 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7d8) = Some W_6b7d8.
Proof. vm_refl. Qed.
Lemma D_6b7d8 : decode_any W_6b7d8 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b7f8 : is_ecall W_6b7d8 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7dc : bv 32 := 0x1017871b.
Lemma F_6b7dc : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7dc) = Some W_6b7dc.
Proof. vm_refl. Qed.
Lemma D_6b7dc : decode_any W_6b7dc = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b7fc : is_ecall W_6b7dc = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7e0 : bv 32 := 0x00255793.
Lemma F_6b7e0 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7e0) = Some W_6b7e0.
Proof. vm_refl. Qed.
Lemma D_6b7e0 : decode_any W_6b7e0 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b800 : is_ecall W_6b7e0 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7e4 : bv 32 := 0x00f56533.
Lemma F_6b7e4 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7e4) = Some W_6b7e4.
Proof. vm_refl. Qed.
Lemma D_6b7e4 : decode_any W_6b7e4 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b804 : is_ecall W_6b7e4 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7e8 : bv 32 := 0x02059793.
Lemma F_6b7e8 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7e8) = Some W_6b7e8.
Proof. vm_refl. Qed.
Lemma D_6b7e8 : decode_any W_6b7e8 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b808 : is_ecall W_6b7e8 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7ec : bv 32 := 0x00f585b3.
Lemma F_6b7ec : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7ec) = Some W_6b7ec.
Proof. vm_refl. Qed.
Lemma D_6b7ec : decode_any W_6b7ec = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b80c : is_ecall W_6b7ec = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7f0 : bv 32 := 0x02061793.
Lemma F_6b7f0 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7f0) = Some W_6b7f0.
Proof. vm_refl. Qed.
Lemma D_6b7f0 : decode_any W_6b7f0 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b810 : is_ecall W_6b7f0 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7f4 : bv 32 := 0x00f60633.
Lemma F_6b7f4 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7f4) = Some W_6b7f4.
Proof. vm_refl. Qed.
Lemma D_6b7f4 : decode_any W_6b7f4 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b814 : is_ecall W_6b7f4 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7f8 : bv 32 := 0x02069793.
Lemma F_6b7f8 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7f8) = Some W_6b7f8.
Proof. vm_refl. Qed.
Lemma D_6b7f8 : decode_any W_6b7f8 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b818 : is_ecall W_6b7f8 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b7fc : bv 32 := 0x00f686b3.
Lemma F_6b7fc : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b7fc) = Some W_6b7fc.
Proof. vm_refl. Qed.
Lemma D_6b7fc : decode_any W_6b7fc = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b81c : is_ecall W_6b7fc = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b800 : bv 32 := 0x02071793.
Lemma F_6b800 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b800) = Some W_6b800.
Proof. vm_refl. Qed.
Lemma D_6b800 : decode_any W_6b800 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b820 : is_ecall W_6b800 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b804 : bv 32 := 0x00f70733.
Lemma F_6b804 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b804) = Some W_6b804.
Proof. vm_refl. Qed.
Lemma D_6b804 : decode_any W_6b804 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b824 : is_ecall W_6b804 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b808 : bv 32 := 0x00455793.
Lemma F_6b808 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b808) = Some W_6b808.
Proof. vm_refl. Qed.
Lemma D_6b808 : decode_any W_6b808 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b828 : is_ecall W_6b808 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b80c : bv 32 := 0x00f56533.
Lemma F_6b80c : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b80c) = Some W_6b80c.
Proof. vm_refl. Qed.
Lemma D_6b80c : decode_any W_6b80c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b82c : is_ecall W_6b80c = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b810 : bv 32 := 0x00855793.
Lemma F_6b810 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b810) = Some W_6b810.
Proof. vm_refl. Qed.
Lemma D_6b810 : decode_any W_6b810 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b830 : is_ecall W_6b810 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b814 : bv 32 := 0x00f56533.
Lemma F_6b814 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b814) = Some W_6b814.
Proof. vm_refl. Qed.
Lemma D_6b814 : decode_any W_6b814 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b834 : is_ecall W_6b814 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b818 : bv 32 := 0x01055793.
Lemma F_6b818 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b818) = Some W_6b818.
Proof. vm_refl. Qed.
Lemma D_6b818 : decode_any W_6b818 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b838 : is_ecall W_6b818 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b81c : bv 32 := 0x00f56533.
Lemma F_6b81c : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b81c) = Some W_6b81c.
Proof. vm_refl. Qed.
Lemma D_6b81c : decode_any W_6b81c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b83c : is_ecall W_6b81c = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b820 : bv 32 := 0x02055793.
Lemma F_6b820 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b820) = Some W_6b820.
Proof. vm_refl. Qed.
Lemma D_6b820 : decode_any W_6b820 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b840 : is_ecall W_6b820 = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b824 : bv 32 := 0x00f56533.
Lemma F_6b824 : fetch_word AsanUbsan.M.loaded_segments (Z_to_bv 64 0x6b824) = Some W_6b824.
Proof. vm_refl. Qed.
Lemma D_6b824 : decode_any W_6b824 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.
Lemma N_6b844 : is_ecall W_6b824 = false.
Proof. vm_compute. reflexivity. Qed.
End Both61h.

Module Both_msb.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan18z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb.Asankdu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z.AsanMsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Both61h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Open Scope Z_scope.

Lemma both_msb_run : forall regs M rom,
  2 ^ 46 <= bv_unsigned (getr regs 10%bv) < 2 ^ 47 ->
  exists regs', msteps AsanUbsan.M.loaded_segments (mkst regs (Z_to_bv 64 MSB_PC_BOTH) M rom)
                       (mkst regs' (Z_to_bv 64 (MSB_PC_BOTH + 112)) M rom)
                /\ msb_post regs regs'.
Proof.
  exact (msb_run AsanUbsan.M.loaded_segments MSB_PC_BOTH ltac:(unfold MSB_PC_BOTH; lia)
           W_6b7b8 W_6b7bc W_6b7c0 W_6b7c4 W_6b7c8 W_6b7cc W_6b7d0 W_6b7d4 W_6b7d8 W_6b7dc W_6b7e0 W_6b7e4 W_6b7e8 W_6b7ec W_6b7f0 W_6b7f4 W_6b7f8 W_6b7fc W_6b800 W_6b804 W_6b808 W_6b80c W_6b810 W_6b814 W_6b818 W_6b81c W_6b820 W_6b824
           F_6b7b8 F_6b7bc F_6b7c0 F_6b7c4 F_6b7c8 F_6b7cc F_6b7d0 F_6b7d4 F_6b7d8 F_6b7dc F_6b7e0 F_6b7e4 F_6b7e8 F_6b7ec F_6b7f0 F_6b7f4 F_6b7f8 F_6b7fc F_6b800 F_6b804 F_6b808 F_6b80c F_6b810 F_6b814 F_6b818 F_6b81c F_6b820 F_6b824
           N_6b7d8 N_6b7dc N_6b7e0 N_6b7e4 N_6b7e8 N_6b7ec N_6b7f0 N_6b7f4 N_6b7f8 N_6b7fc N_6b800 N_6b804 N_6b808 N_6b80c N_6b810 N_6b814 N_6b818 N_6b81c N_6b820 N_6b824 N_6b828 N_6b82c N_6b830 N_6b834 N_6b838 N_6b83c N_6b840 N_6b844
           D_6b7b8 D_6b7bc D_6b7c0 D_6b7c4 D_6b7c8 D_6b7cc D_6b7d0 D_6b7d4 D_6b7d8 D_6b7dc D_6b7e0 D_6b7e4 D_6b7e8 D_6b7ec D_6b7f0 D_6b7f4 D_6b7f8 D_6b7fc D_6b800 D_6b804 D_6b808 D_6b80c D_6b810 D_6b814 D_6b818 D_6b81c D_6b820 D_6b824).
Qed.
End Both_msb.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanoq0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99.Asanfrq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asang2p.Asann85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asang2p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asang2p.Asanku0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Sums618 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanj99 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Asanc52 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb.Asankdu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothy0u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z.AsanMsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z.Asanpid OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan18z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothmmq.Both_msb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma XE0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
Lemma XSniff_vacuous : forall (nx0 : nat) (LIMIT : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs),
    x_stmt BSEGS BOTH nx0 LIMIT SINV argH FS0 XSniff.
Proof. intros ? ? ? ? ?. intros args cs cs' E R FULL model T _ _ H. discriminate H. Qed.

Section Run.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid nofile sigmask hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  Variable urandom : InputStream.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk BSEGS brk0.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (E0 BPH sp rdraw brk0 argv envp uid hw).
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  #[local] Notation LIM := (@AsanInit.blim BL).

  (* [comment removed for export] *)
  Let AH : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a := argH0_high BPH sp rdraw argv envp uid hw Hsp Hva.
  Let SF : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M' := SINV0_frame BPH sp rdraw brk0 argv envp uid hw.
  Let AT : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a :=
    argH0_top BPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.

  Section AnyNx0.
    (* [comment removed for export] *)
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.

    Let NXok : nx0_ok nx0 := nx0_ok_n nx0 Hnx0.
    Let AA : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a := argH0_agree_n sp rdraw argv envp uid hw nx0.
    Let SA : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M := SINV0_agree_n sp rdraw brk0 argv envp uid hw nx0 Hnx0.

    (* [comment removed for export] *)
    Theorem both_node_x_sound_all : forall x, x_stmt BSEGS BOTH nx0 LIM SINV argH fs x.
    Proof.
      intros [ | | | | | | | | | | ].
      - apply (both_node_x_sound_XIMemset nx0 LIM SINV _ AH AA SF SA NXok fs).
      - apply (both_node_x_sound_XIMemcpy nx0 LIM SINV _ AH AA SF SA NXok fs).
      - apply (both_node_x_sound_XMemset nx0 LIM SINV _ AH AA SF SA NXok fs).
      - apply (both_node_x_sound_XMemcpy nx0 LIM SINV _ AH AA SF SA NXok fs).
      - apply (both_node_x_sound_XMemIsZero nx0 LIM SINV _ AH AA SF SA NXok fs).
      - apply (node_x_sound_XEnvScan_asan sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit nx0 Hnx0).
      - apply (node_x_sound_XPnScan_asan sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit nx0 Hnx0).
      - apply (node_x_sound_XLayout_asan sp rdraw brk0 argv envp fs uid hw nx0).
      - apply (both_node_x_sound_XIStrncpy nx0 LIM SINV _ AH AA SF SA NXok fs).
      - apply (both_node_x_sound_XPopFree nx0 LIM SINV _ AH AA SF SA NXok fs).
      - apply XSniff_vacuous.
    Qed.

    (* [comment removed for export] *)
    Theorem both_XN_sound : ext_stmt BSEGS BOTH nx0 LIM (XNb2 nx0) SINV argH fs.
    Proof.
      apply (XN2_sound BSEGS BOTH nx0 LIM SINV argH fs both_in_hull both_hull_ok MSB_PC_BOTH).
      exact (XN1_sound BSEGS BOTH nx0 LIM SINV argH fs both_wx both_in_hull both_hull_ok NXok AA SF SA
               MSB_PC_BOTH both_msb_run).
    Qed.

    (* [comment removed for export] *)
    Theorem both_check_sound :
      forall (IT : itab) (IT_ok : itab_sound BSEGS IT) (HS : nat -> option acs)
             (HOLES : nat -> env -> Fs.Fs -> TSet)
             (HOLES_agree : forall h E E' fs', env_agree nx0 E E' -> HOLES h E fs' = HOLES h E' fs')
             (HOLES_nil : forall h E fs', HOLES h E fs' [])
             (HOLES_sound : holes_stmt BSEGS BOTH LIM HS SINV argH HOLES fs)
             (KC BFUEL FUEL : nat) (p : plan) (cs : acs) (s : shape),
        check BSEGS IT BOTH nx0 LIM (XNb2 nx0) XE0 XB0 HS KC BFUEL FUEL None cs p = COk s ->
        forall E R FULL model,
          cs_ok BSEGS BOTH LIM SINV argH fs E cs R FULL model ->
          srealizes BSEGS (cfg_of BSEGS R (pc cs) FULL model) (sd HOLES t_nil E (m_fs model) s).
    Proof.
      intros IT IT_ok HS HOLES HOLES_agree HOLES_nil HOLES_sound KC BFUEL FUEL p cs s Hc E R FULL model HC.
      exact (check_sound BSEGS IT IT_ok BOTH nx0 LIM HS (XNb2 nx0) XE0 XB0
               both_wx both_in_hull both_hull_ok both_shadow_ok NXok SINV argH AH AA SF SA
               HOLES HOLES_agree HOLES_nil fs KC
               (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asang2p.Asanku0.node_sys_sound BSEGS BOTH nx0 LIM SINV argH fs both_res_len both_hull_ok both_shadow_ok AA SF SA NXok AT)
               (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asang2p.Asanku0.node_brk2_sound BSEGS BOTH nx0 LIM SINV argH fs both_in_hull both_hull_ok both_shadow_ok AH SF
                  both_res_cover both_shadow_val AT both_res_len)
               (node_mmap2_sound_OBL BSEGS BOTH nx0 LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok
                  AH AA SF SA both_res_cover both_shadow_val NXok AT)
               (node_mmapin_sound_OBL BSEGS BOTH nx0 LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok
                  AH AA SF SA both_res_cover both_shadow_val NXok AT)
               (node_mprotect2_sound_OBL BSEGS BOTH nx0 LIM SINV argH fs both_in_hull both_res_len both_res_hull both_hull_ok both_shadow_ok
                  AH AA SF SA both_res_cover both_shadow_val NXok AT)
               (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asang2p.Asanku0.node_exit_sound BSEGS BOTH LIM SINV argH fs)
               both_node_x_sound_all
               (node_join_sound BSEGS BOTH nx0 LIM SINV argH fs)
               both_XN_sound (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
               HOLES_sound FUEL BFUEL None p cs s Hc
               E R FULL model t_nil HC I eq_refl).
    Qed.
  End AnyNx0.

  (* [comment removed for export] *)
  Theorem both_startup :
    forall (IT : itab) (IT_ok : itab_sound BSEGS IT) (HS : nat -> option acs)
           (HOLES : nat -> env -> Fs.Fs -> TSet)
           (HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs')
           (HOLES_nil : forall h E fs', HOLES h E fs' [])
           (HOLES_sound : holes_stmt BSEGS BOTH LIM HS SINV argH HOLES fs)
           (KC BFUEL FUEL : nat) (p : plan) (s : shape),
      check BSEGS IT BOTH NX0 LIM (XNb2 NX0) XE0 XB0 HS KC BFUEL FUEL None both_init p = COk s ->
      forall apc : N, Z.of_N apc = a_entry BOTH ->
      srealizes BSEGS (init_config BSEGS apc BPH sp brk0 mbase rdraw LIM (AsanInit.inp argv envp fs stdin uid gid nofile sigmask hw groups net urandom))
                (sd HOLES t_nil E0a fs s).
  Proof.
    intros IT IT_ok HS HOLES HOLES_agree HOLES_nil HOLES_sound KC BFUEL FUEL p s Hc apc Hapc.
    rewrite (init_cfg_eq BSEGS BOTH BPH sp rdraw brk0 mbase argv envp fs stdin uid gid nofile sigmask hw groups net urandom apc Hapc).
    pose proof (init_cs_ok BSEGS BOTH BPH sp rdraw brk0 mbase argv envp fs stdin uid gid nofile sigmask hw groups net urandom
                  both_img_facts Hsp Hbrk Hva Hve Hfit Huid Hhw) as HC.
    pose proof (both_check_sound NX0 (le_n NX0) IT IT_ok HS HOLES HOLES_agree HOLES_nil HOLES_sound KC BFUEL FUEL p both_init s Hc
                  _ _ _ _ HC) as RZ.
    exact RZ.
  Qed.
End Run.
