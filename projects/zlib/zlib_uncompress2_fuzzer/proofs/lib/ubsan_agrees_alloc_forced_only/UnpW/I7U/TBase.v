(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7U Require Export Base.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Export ZArr ZArr4 ZRd IDefs IMem ITac ISpecs IGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ROMHI_T : Z := 139264.     (* [comment removed for export] *)
Definition FR_INF : Z := 256.         (* [comment removed for export] *)
Definition FR_UW : Z := 64.           (* [comment removed for export] *)
Definition FR_IT : Z := 208.          (* [comment removed for export] *)
Definition FR_IF : Z := 160.          (* [comment removed for export] *)
Definition FR_AD : Z := 128.          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_INFLATE : Z := 86740.   (* [comment removed for export] *)
Definition L_DISP    : Z := 87108.   (* [comment removed for export] *)
Definition L_REDISP  : Z := 88676.   (* a worker 1.4 UBSan: 0x159d8, the trampoline (mv a3; ld a1,136(sp); j disp) *)
Definition L_REDISP_A1 : Z := 91144. (* [comment removed for export] *)
Definition L_BADMSG_A0 : Z := 91128. (* [comment removed for export] *)
Definition L_BADMSG_A5 : Z := 90396. (* [comment removed for export] *)
Definition L_BADMSG_A5B : Z := 90404. (* [comment removed for export] *)
Definition L_BADMSG_A1 : Z := 95920. (* [comment removed for export] *)
Definition L_LEAVE   : Z := 96464.   (* [comment removed for export] *)
Definition L_LEAVE_LD : Z := 96308.  (* [comment removed for export] *)
Definition L_LEAVE_LD2 : Z := 96452. (* [comment removed for export] *)
Definition L_LEAVE_L0 : Z := 96448.  (* [comment removed for export] *)
(* [comment removed for export] *)  (* [comment removed for export] *)
Definition L_RET     : Z := 96956.   (* [comment removed for export] *)
Definition L_RET_S10 : Z := 96952.   (* [comment removed for export] *)
Definition L_NEED_DICT : Z := 96316. (* a worker 1.4 UBSan: 0x177ac, DICTID's Z_NEED_DICT exit (1.4 adds the total_in update) *)
Definition L_MEM     : Z := 96536.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_HEAD : Z := 87160.      (* [comment removed for export] *)
Definition L_DICTID : Z := 87492.    (* [comment removed for export] *)
Definition L_DICT : Z := 88180.      (* [comment removed for export] *)
Definition L_TYPE : Z := 88240.      (* [comment removed for export] *)
Definition L_TYPEDO : Z := 88256.    (* [comment removed for export] *)
Definition L_STORED : Z := 87612.    (* [comment removed for export] *)
Definition L_COPY_ : Z := 88492.     (* [comment removed for export] *)
Definition L_COPY : Z := 88500.      (* [comment removed for export] *)
Definition L_TABLE : Z := 87872.     (* [comment removed for export] *)
Definition L_LENLENS : Z := 87464.   (* [comment removed for export] *)
Definition L_CODELENS : Z := 89264.  (* [comment removed for export] *)
Definition L_LEN_ : Z := 93628.      (* [comment removed for export] *)
Definition L_LEN : Z := 93636.       (* [comment removed for export] *)
Definition L_LENEXT : Z := 87332.    (* [comment removed for export] *)
Definition L_DIST : Z := 94428.      (* [comment removed for export] *)
Definition L_DISTEXT : Z := 87480.   (* [comment removed for export] *)
Definition L_MATCH : Z := 95244.     (* [comment removed for export] *)
Definition L_LIT : Z := 87268.       (* [comment removed for export] *)
Definition L_CHECK : Z := 87976.     (* [comment removed for export] *)
Definition L_LENGTH : Z := 92392.    (* [comment removed for export] *)
Definition L_DONE : Z := 96440.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition L_UW : Z := 97060.        (* [comment removed for export] *)
Definition L_UW_CALL : Z := 96516.   (* [comment removed for export] *)
Definition L_UW_RET : Z := 96520.    (* [comment removed for export] *)
Definition T_ZW : Z := 97168.        (* [comment removed for export] *)
Definition L_ZB : Z := 97172.        (* [comment removed for export] *)
Definition L_ITABLE : Z := 99048.    (* [comment removed for export] *)
Definition L_IFAST : Z := 103336.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition s_fix (cx : ictx) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -256 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kA3 = c_u cx /\ zget_l Rb l kS1 = c_u cx /\
  zget_l Rb l kA1 = 0 /\ zget_l Rb l kRA = 16209.

(* [comment removed for export] *)
Definition s_vars (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kS10 = c_q cx + t_cin st /\ zget_l Rb l kS8 = c_n cx - t_cin st /\
  zget_l Rb l kS3 = c_ob cx + t_cout st /\ zget_l Rb l kS4 = t_hold st /\ zget_l Rb l kS2 = t_bits st.

(* [comment removed for export] *)
Definition s_regs_disp (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l.
(* [comment removed for export] *)
Definition s_regs_arm (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  s_fix cx Rb l /\ s_vars cx st Rb l /\ zget_l Rb l kS11 = -3.
(* [comment removed for export] *)
Definition s_regs_leave (cx : ictx) (st : ist) (rv : Z) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -256 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kA3 = c_u cx /\ zget_l Rb l kS1 = c_u cx /\ zget_l Rb l kA1 = 0 /\
  zget_l Rb l kS10 = c_q cx + t_cin st /\ zget_l Rb l kS8 = c_n cx - t_cin st /\
  zget_l Rb l kS3 = c_ob cx + t_cout st /\ zget_l Rb l kS4 = t_hold st /\ zget_l Rb l kS2 = t_bits st /\
  zget_l Rb l kS11 = rv.
(* [comment removed for export] *)
Definition s_regs_leave_ld (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -256 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kA3 = c_u cx /\ zget_l Rb l kS1 = c_u cx /\ zget_l Rb l kA1 = 0 /\
  zget_l Rb l kS10 = c_q cx + t_cin st /\ zget_l Rb l kS8 = c_n cx - t_cin st /\
  zget_l Rb l kS3 = c_ob cx + t_cout st /\ zget_l Rb l kS4 = t_hold st /\ zget_l Rb l kS2 = t_bits st.
(* [comment removed for export] *)
Definition s_regs_leave_ld2 (cx : ictx) (st : ist) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -256 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_p cx /\ zget_l Rb l kS1 = c_u cx /\
  zget_l Rb l kS10 = c_q cx + t_cin st /\ zget_l Rb l kS8 = c_n cx - t_cin st /\
  zget_l Rb l kS3 = c_ob cx + t_cout st /\ zget_l Rb l kS4 = t_hold st /\ zget_l Rb l kS2 = t_bits st.
(* [comment removed for export] *)
Definition s_regs_ret (cx : ictx) (rc : Z) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx + -256 /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kA0 = rc.
(* [comment removed for export] *)
Definition s_regs_entry (cx : ictx) (Rb : tree Z) (l : list (positive * Z)) : Prop :=
  zget_l Rb l kSP = c_u cx /\ zget_l Rb l kA0 = c_u cx /\ zget_l Rb l kA1 = 0 /\
  zget_l Rb l kRA = c_K cx kRA /\ zget_l Rb l kGP = c_K cx kGP /\ zget_l Rb l kTP = c_K cx kTP /\
  zget_l Rb l kS0 = c_K cx kS0 /\ zget_l Rb l kS1 = c_K cx kS1 /\ zget_l Rb l kS2 = c_K cx kS2 /\
  zget_l Rb l kS3 = c_K cx kS3 /\ zget_l Rb l kS4 = c_K cx kS4 /\ zget_l Rb l kS5 = c_K cx kS5 /\
  zget_l Rb l kS6 = c_K cx kS6 /\ zget_l Rb l kS7 = c_K cx kS7 /\ zget_l Rb l kS8 = c_K cx kS8 /\
  zget_l Rb l kS9 = c_K cx kS9 /\ zget_l Rb l kS10 = c_K cx kS10 /\ zget_l Rb l kS11 = c_K cx kS11.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition i_frame {RCa1 : RunCtx}  (cx : ictx) (M : mem) : Prop :=
  let u := c_u cx in let p := c_p cx in let K := c_K cx in
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -8) (K kRA) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -16) (K kS0) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -24) (K kS1) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -32) (K kS2) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -40) (K kS3) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -48) (K kS4) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -56) (K kS5) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -64) (K kS6) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -72) (K kS7) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -80) (K kS8) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -88) (K kS9) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -96) (K kS10) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -104) (K kS11) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -120) 0 /\                       (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -128) (p + 168) /\               (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -136) (- (p + 168) + -1) /\      (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -144) (-16180) /\                (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -152) JTAB_ADDR /\               (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -176) 16209 /\                   (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -192) (c_n cx - c_cin0 cx) /\    (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -200) (p + 7160) /\              (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -208) (-5) /\                    (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -216) (p + 160) /\               (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -224) (p + 808) /\               (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -232) (p + 1384) /\              (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -240) (p + 136) /\               (* [comment removed for export] *)
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -248) (p + 140).                 (* [comment removed for export] *)
(* [comment removed for export] *)
Definition s_ret {RCa1 : RunCtx}  (cx : ictx) (st : ist) (M : mem) : Prop := mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -184) (t_ret st).
(* [comment removed for export] *)
Definition s_lo {RCa1 : RunCtx}  (cx : ictx) (st : ist) (M : mem) : Prop :=
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -160) (c_osz cx - t_cout st) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -168) (t_out st).
(* [comment removed for export] *)
Definition s_bk {RCa1 : RunCtx}  (cx : ictx) (st : ist) (M : mem) : Prop :=
  exists c, mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 7164) c /\ 0 <= c /\
            (t_mode st = LENEXT -> c <= 64) /\ (t_mode st = DIST -> c <= 128).
Lemma s_bk_intro {RCa1 : RunCtx}  : forall cx st M c,
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 7164) c -> 0 <= c ->
  (t_mode st = LENEXT -> c <= 64) -> (t_mode st = DIST -> c <= 128) -> s_bk cx st M.
Proof. intros cx st M c H H0 H1 H2. exists c. split; [exact H | split; [exact H0 | split; assumption]]. Qed.
Lemma s_bk_other {RCa1 : RunCtx}  : forall cx st st' M,
  s_bk cx st M -> t_mode st' <> LENEXT -> t_mode st' <> DIST -> s_bk cx st' M.
Proof.
  intros cx st st' M (c & H & H0 & _ & _) N1 N2. exists c. split; [exact H | split; [exact H0 |]].
  split; intros E; exfalso; [exact (N1 E) | exact (N2 E)].
Qed.
Lemma s_bk_same {RCa1 : RunCtx}  : forall cx st st' M, s_bk cx st M -> t_mode st' = t_mode st -> s_bk cx st' M.
Proof. intros cx st st' M (c & H & H0 & H1 & H2) E. exists c. rewrite E. split; [exact H | split; [exact H0 | split; assumption]]. Qed.
(* [comment removed for export] *)
Lemma s_bk_free {RCa1 : RunCtx}  : forall cx st M,
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx) STATE_SIZE -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  t_mode st <> LENEXT -> t_mode st <> DIST -> s_bk cx st M.
Proof.
  intros cx st M W Hp0 Hp1 N1 N2. unfold STATE_SIZE in *.
  destruct (mem_wr_u32_exists_R M (c_p cx + 7164) ltac:(eapply mem_wr_sub; [exact W | lia_std | lia_std])) as (c & Hc & Rc).
  exists c. split; [exact Hc | split; [lia_std |]]. split; intros E; exfalso; [exact (N1 E) | exact (N2 E)].
Qed.

(* [comment removed for export] *)
Definition i_frame_ok (cx : ictx) (a k : Z) : Prop :=
  a + k <= c_u cx + -248 \/ c_u cx <= a \/
  (c_u cx + -184 <= a /\ a + k <= c_u cx + -176) \/ (c_u cx + -168 <= a /\ a + k <= c_u cx + -160) \/
  (c_u cx + -160 <= a /\ a + k <= c_u cx + -152) \/ (c_u cx + -112 <= a /\ a + k <= c_u cx + -104).

Lemma i_frame_frame {RCa1 : RunCtx}  : forall cx M a bs,
  i_frame cx M -> 0 <= c_u cx + -1024 -> c_u cx + 208 <= two64 -> 0 <= a -> 0 < Z.of_nat (length bs) -> a + Z.of_nat (length bs) <= two64 ->
  i_frame_ok cx a (Z.of_nat (length bs)) ->
  i_frame cx (wbytes M (w64 a) bs).
Proof.
  intros cx M a bs H Hu1 Hu2 Ha Hl Ha2 D. unfold i_frame, i_frame_ok in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
  repeat split; (apply mem_u64_frame; [assumption | unfold zdisj; lia_std]).
Qed.

Lemma i_frame_magreeL {RCa1 : RunCtx}  : forall cx M0 M rs,
  magreeL M0 M rs -> i_frame cx M0 -> 0 <= c_u cx + -1024 -> c_u cx + 208 <= two64 ->
  disj_all (c_u cx + -248) 64 rs -> disj_all (c_u cx + -176) 8 rs -> disj_all (c_u cx + -152) 16 rs ->
  disj_all (c_u cx + -136) 24 rs -> disj_all (c_u cx + -104) 104 rs ->
  i_frame cx M.
Proof.
  intros cx M0 M rs HA H Hu1 Hu2 D1 D2 D3 D4 D5. unfold i_frame in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
  repeat split;
    (eapply mem_u64_magreeL;
     [ exact HA | eassumption | lia_std | lia_std
     | first [ solve [eapply (disj_all_sub rs); [exact D1 | lia_std | lia_std]]
             | solve [eapply (disj_all_sub rs); [exact D2 | lia_std | lia_std]]
             | solve [eapply (disj_all_sub rs); [exact D3 | lia_std | lia_std]]
             | solve [eapply (disj_all_sub rs); [exact D4 | lia_std | lia_std]]
             | solve [eapply (disj_all_sub rs); [exact D5 | lia_std | lia_std]] ] ]).
Qed.

Lemma s_lo_magreeL {RCa1 : RunCtx}  : forall cx st M0 M rs,
  magreeL M0 M rs -> s_lo cx st M0 -> 0 <= c_u cx + -1024 -> c_u cx + 208 <= two64 ->
  disj_all (c_u cx + -160) 8 rs -> disj_all (c_u cx + -168) 8 rs -> s_lo cx st M.
Proof.
  intros cx st M0 M rs HA [A B] Hu1 Hu2 D1 D2.
  split; (eapply mem_u64_magreeL; [exact HA | eassumption | lia_std | lia_std
          | first [ solve [eapply (disj_all_sub rs); [exact D1 | lia_std | lia_std]]
                  | solve [eapply (disj_all_sub rs); [exact D2 | lia_std | lia_std]] ] ]).
Qed.
Lemma s_bk_magreeL {RCa1 : RunCtx}  : forall cx st M0 M rs,
  magreeL M0 M rs -> s_bk cx st M0 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  disj_all (c_p cx + 7164) 4 rs -> s_bk cx st M.
Proof.
  intros cx st M0 M rs HA (c & A & B) Hp1 Hp2 D. unfold STATE_SIZE in *. exists c. split; [| exact B].
  eapply mem_u32_magreeL; [exact HA | exact A | lia_std | lia_std | exact D].
Qed.

(* [comment removed for export] *)
Definition i_hooks {RCa1 : RunCtx}  (cx : ictx) (M : mem) : Prop :=
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + 64) A_ZCALLOC /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + 72) A_ZCFREE.
Lemma i_hooks_frame {RCa1 : RunCtx}  : forall cx M a bs,
  i_hooks cx M -> 0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= a -> 0 < Z.of_nat (length bs) -> a + Z.of_nat (length bs) <= two64 ->
  (a + Z.of_nat (length bs) <= c_u cx + 56 \/ c_u cx + 88 <= a) ->
  i_hooks cx (wbytes M (w64 a) bs).
Proof.
  intros cx M a bs [A B] Hu1 Hu2 Ha Hl Ha2 D. split; (apply mem_u64_frame; [assumption | unfold zdisj; lia_std]).
Qed.
Lemma i_hooks_magreeL {RCa1 : RunCtx}  : forall cx M0 M rs,
  magreeL M0 M rs -> i_hooks cx M0 -> 0 <= c_u cx -> c_u cx + 208 <= two64 -> disj_all (c_u cx + 56) 32 rs -> i_hooks cx M.
Proof.
  intros cx M0 M rs HA [A B] Hu1 Hu2 D.
  split; (eapply mem_u64_magreeL; [exact HA | eassumption | lia_std | lia_std | eapply (disj_all_sub rs); [exact D | lia_std | lia_std]]).
Qed.

(* [comment removed for export] *)
Definition wb_bounds (u p a len : Z) : Prop :=
  0 <= u + -1024 /\ u + 208 <= two64 /\ 0 <= p /\ p + STATE_SIZE <= two64 /\ 0 <= a /\ 0 < len /\ a + len <= two64.
Lemma i_frame_frame1 {RCa1 : RunCtx}  : forall cx M a bs,
  i_frame cx M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) -> i_frame_ok cx a (Z.of_nat (length bs)) ->
  i_frame cx (wbytes M (w64 a) bs).
Proof. intros cx M a bs H (B1 & B2 & B3 & B4 & B5 & B6 & B7) D. apply i_frame_frame; assumption. Qed.
Lemma i_hooks_frame1 {RCa1 : RunCtx}  : forall cx M a bs,
  i_hooks cx M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_u cx + 56 \/ c_u cx + 88 <= a) -> i_hooks cx (wbytes M (w64 a) bs).
Proof. intros cx M a bs H (B1 & B2 & B3 & B4 & B5 & B6 & B7) D. apply i_hooks_frame; try assumption. lia_std. Qed.
Lemma i_cst_frame1 {RCa1 : RunCtx}  : forall cx M a bs,
  i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_u cx + 56 \/ c_u cx + 88 <= a) ->
  (a + Z.of_nat (length bs) <= c_p cx \/ (c_p cx + 8 <= a /\ a + Z.of_nat (length bs) <= c_p cx + 16) \/
   (c_p cx + 24 <= a /\ a + Z.of_nat (length bs) <= c_p cx + 56) \/ (c_p cx + 76 <= a /\ a + Z.of_nat (length bs) <= c_p cx + 88) \/
   (c_p cx + 96 <= a /\ a + Z.of_nat (length bs) <= c_p cx + 7160) \/ c_p cx + 7164 <= a) ->
  i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx (wbytes M (w64 a) bs).
Proof. intros cx M a bs H (B1 & B2 & B3 & B4 & B5 & B6 & B7) D1 D2. apply i_cst_frame; try assumption; [lia_std | split; assumption]. Qed.
(* [comment removed for export] *)
Definition st_hole (p a k : Z) : Prop :=
  (p + 16 <= a /\ a + k <= p + 28) \/ (p + 32 <= a /\ a + k <= p + 76) \/ (p + 88 <= a /\ a + k <= p + 108) \/ p + 168 <= a.
Lemma st_rest_frameH {RCa1 : RunCtx}  : forall cx st M a bs,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_p cx + 12 \/ st_hole (c_p cx) a (Z.of_nat (length bs))) ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st (wbytes M (w64 a) bs).
Proof.
  intros cx st M a bs H (B1 & B2 & B3 & B4 & B5 & B6 & B7) D. unfold st_rest, st_hole, STATE_SIZE in *.
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; ((apply mem_u64_frame || apply mem_u32_frame); [assumption | unfold zdisj; lia_std]).
Qed.
Lemma st_at_frameH {RCa1 : RunCtx}  : forall cx st M a bs,
  st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_p cx + 8 \/ st_hole (c_p cx) a (Z.of_nat (length bs))) ->
  st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st (wbytes M (w64 a) bs).
Proof.
  intros cx st M a bs [Hm H] HB D. split.
  - dand HB as (B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold st_hole, STATE_SIZE in *.
    apply mem_u32_frame; [exact Hm | unfold zdisj; lia_std].
  - apply st_rest_frameH; [exact H | exact HB | unfold st_hole in *; lia_std].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma strm_at_frameH {RCa1 : RunCtx}  : forall cx st M a bs,
  strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_u cx \/ (c_u cx + 12 <= a /\ a + Z.of_nat (length bs) <= c_u cx + 24) \/ c_u cx + 36 <= a) ->
  (a + Z.of_nat (length bs) <= c_p cx + 96 \/ c_p cx + 108 <= a) -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st (wbytes M (w64 a) bs).
Proof.
  intros cx st M a bs H (B1 & B2 & B3 & B4 & B5 & B6 & B7) D1 D2. unfold strm_at, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; ((apply mem_u64_frame || apply mem_u32_frame); [assumption | unfold zdisj; lia_std]).
Qed.
(* [comment removed for export] *)
Lemma s_lo_frame {RCa1 : RunCtx}  : forall cx st M a bs,
  s_lo cx st M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_u cx + -168 \/ (c_u cx + -152 <= a /\ a + Z.of_nat (length bs) <= c_u cx + -144) \/ c_u cx + -152 <= a) ->
  s_lo cx st (wbytes M (w64 a) bs).
Proof.
  intros cx st M a bs [A B] (B1 & B2 & B3 & B4 & B5 & B6 & B7) D.
  split; (apply mem_u64_frame; [assumption | unfold zdisj; lia_std]).
Qed.
Lemma s_bk_frame1 {RCa1 : RunCtx}  : forall cx st M a bs,
  s_bk cx st M -> wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs)) ->
  (a + Z.of_nat (length bs) <= c_p cx + 7164 \/ c_p cx + 7168 <= a) -> s_bk cx st (wbytes M (w64 a) bs).
Proof.
  intros cx st M a bs (c & A & B) (B1 & B2 & B3 & B4 & B5 & B6 & B7) D. unfold STATE_SIZE in *.
  exists c. split; [| exact B]. apply mem_u32_frame; [exact A | unfold zdisj; lia_std].
Qed.
Lemma rom_ok_frame1 : forall M a bs,
  rom_ok M -> (0 <= a /\ a + Z.of_nat (length bs) <= two64) -> zdisj a (Z.of_nat (length bs)) ROM_LO (ROM_HI - ROM_LO) ->
  rom_ok (wbytes M (w64 a) bs).
Proof. intros M a bs H [B1 B2] D. apply rom_ok_frame; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition s_std {RCa1 : RunCtx}  (cx : ictx) (fin : Z -> Z) (M : mem) : Prop :=
  rom_ok M /\
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -1024) 1232 /\      (* [comment removed for export] *)
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx) STATE_SIZE /\
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_ob cx) (c_osz cx) /\
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (c_w cx) (wsz cx) /\          (* [comment removed for export] *)
  i_frame cx M /\ i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx M /\ i_hooks cx M /\
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_q cx) (c_n cx) fin.

(* [comment removed for export] *)
Ltac open_std H :=
  dand H as (ROM & Wstk & Wp & Wob & Ww & FRM & CST & HK & Hin).
Ltac close_std := unfold s_std; icx_cbn; split_conj; assumption.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zbare_refuted :=
  match goal with |- ?G =>
    let X := fresh in
    assert (X : ~ G) by (repeat match goal with K : _ |- _ => clear K end; Zify.zify; xlia zchecker)
  end.
Ltac zlia_chkb := tryif zbare_refuted then fail else zlia.
Ltac zdisj_tac ::= unfold zdisj; zlen_fast; first [ zlia_chkb | zlen_norm; zlia_chkb ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zwb_x a :=
  first [ lazymatch goal with |- ?G => match goal with W : G |- _ => exact W end end
        | unfold wb_bounds; icx_cbn; cbv [STATE_SIZE]; zlen_norm; zlia ].
Ltac zwb_pre M a bs :=
  try (let W := fresh "ZWBs" in
       lazymatch goal with
       | H : i_frame ?cx M |- _ => assert (W : wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs))) by (unfold wb_bounds; icx_cbn; cbv [STATE_SIZE]; zlen_norm; zlia)
       | H : i_cst _ ?cx M |- _ => assert (W : wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs))) by (unfold wb_bounds; icx_cbn; cbv [STATE_SIZE]; zlen_norm; zlia)
       | H : st_rest _ ?cx _ M |- _ => assert (W : wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs))) by (unfold wb_bounds; icx_cbn; cbv [STATE_SIZE]; zlen_norm; zlia)
       | H : st_at _ ?cx _ M |- _ => assert (W : wb_bounds (c_u cx) (c_p cx) a (Z.of_nat (length bs))) by (unfold wb_bounds; icx_cbn; cbv [STATE_SIZE]; zlen_norm; zlia)
       end).
Ltac zwb_post a := repeat match goal with W : wb_bounds _ _ a (Z.of_nat (length _)) |- _ => clear W end.
Ltac zmem_transport_loop_TBase M a bs :=
  repeat match goal with
  | H : i_frame ?cx M |- _ =>
      first [ apply (i_frame_frame1 cx M a bs) in H;
              [| zwb_x a | unfold i_frame_ok; icx_cbn; zlen_norm; zlia_chkb ]
            | idtac "WARNING: i_frame dropped at store" a; clear H ]
  | H : i_cst ?segs ?cx M |- _ =>
      first [ apply (i_cst_frame1 cx M a bs) in H;
              [| zwb_x a | icx_cbn; zlen_norm; zlia_chkb | icx_cbn; zlen_norm; zlia_chkb ]
            | idtac "WARNING: i_cst dropped at store" a; clear H ]
  | H : i_hooks ?cx M |- _ =>
      first [ apply (i_hooks_frame1 cx M a bs) in H;
              [| zwb_x a | icx_cbn; zlen_norm; zlia_chkb ]
            | idtac "WARNING: i_hooks dropped at store" a; clear H ]
  | H : st_at ?segs ?cx ?st M |- _ =>
      first [ apply (st_at_frameH cx st M a bs) in H;
              [| zwb_x a | unfold st_hole; icx_cbn; zlen_norm; zlia_chkb ]
            | idtac "NOTE: st_at dropped at store (open it before writing state fields)" a; clear H ]
  | H : st_rest ?segs ?cx ?st M |- _ =>
      first [ apply (st_rest_frameH cx st M a bs) in H;
              [| zwb_x a | unfold st_hole; icx_cbn; zlen_norm; zlia_chkb ]
            | idtac "NOTE: st_rest dropped at store (open it before writing state fields other than mode)" a; clear H ]
  | H : strm_at ?segs ?cx ?st M |- _ =>
      first [ apply (strm_at_frameH cx st M a bs) in H;
              [| zwb_x a | icx_cbn; zlen_norm; zlia_chkb | icx_cbn; zlen_norm; zlia_chkb ]
            | idtac "NOTE: strm_at dropped at store" a; clear H ]
  | H : s_ret ?cx ?st M |- _ =>
      first [ unfold s_ret in H; apply (mem_u64_frame _ M a bs) in H; [|icx_cbn; zdisj_tac]; change (s_ret cx st (wbytes M (w64 a) bs)) in H
            | idtac "NOTE: s_ret dropped at store" a; clear H ]
  | H : s_lo ?cx ?st M |- _ =>
      first [ apply (s_lo_frame cx st M a bs) in H; [| zwb_x a | icx_cbn; zlen_norm; zlia_chkb ]
            | idtac "NOTE: s_lo dropped at store (open it before writing left/out)" a; clear H ]
  | H : s_bk ?cx ?st M |- _ =>
      first [ apply (s_bk_frame1 cx st M a bs) in H; [| zwb_x a | icx_cbn; zlen_norm; zlia_chkb ]
            | idtac "NOTE: s_bk dropped at store (the back cell p+7164 was written: re-establish it with s_bk_intro)" a; clear H ]
  | H : mem_arr ?k ?segs M ?base ?n ?f |- _ =>
      first [ apply (mem_arr_frame segs k M base n f a bs) in H; [|unfold zdisj; zlen_norm; zlia_chkb]
            | idtac "WARNING: mem_arr fact dropped at store" a base; clear H ]
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 8;
      first [ apply (mem_u64_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 4;
      first [ apply (mem_u32_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 2;
      first [ apply (mem_u16_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      zrng_ensure a' 1;
      first [ apply (mem_u8_frame segs M a bs a' e) in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      zrng_ensure a' (Z.of_nat (length bs'));
      first [ apply (mem_is_frame segs M a bs a' bs') in H; [|zdisj_x zdisj_tac] | clear H ]
  | H : mem_zero ?segs M ?a' ?len |- _ =>
      first [ apply (mem_zero_frame segs M a bs a' len) in H; [|zdisj_tac]
            | let H1 := fresh "Zl" in let H2 := fresh "Zh" in
              destruct (mem_zero_split_store segs M a bs a' len H ltac:(zlia) ltac:(zlen_norm; zlia) ltac:(zlia) ltac:(zlia) ltac:(zlen_norm; zlia)) as [H1 H2];
              clear H;
              rewrite ?length_app, ?repeat_length, ?length_map, ?length_Z_to_le_bytes', ?Nat2Z.inj_add in H2;
              cbn [length] in H1, H2; znat_lits_in H1; znat_lits_in H2; zfold_in H1; zfold_in H2;
              znorm_zero_len H1; znorm_zero_len H2;
              try (lazymatch type of H1 with mem_zero _ _ _ ?z => lazymatch z with 0 => clear H1 end end);
              try (lazymatch type of H2 with mem_zero _ _ _ ?z => lazymatch z with 0 => clear H2 end end)
            | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      apply (mem_wr_frame segs M a bs a' len) in H
  | H : rom_ok M |- _ =>
      first [ apply (rom_ok_frame1 M a bs) in H; [| zlen_norm; zlia | unfold ROM_LO, ROM_HI; zdisj_tac]
            | idtac "WARNING: rom_ok dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable ?Fr ?lo ?hi |- _ =>
      first [ apply (HS M a bs) in H; [|zlia|zlen_norm; zlia]
            | idtac "WARNING: framed fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable2 ?Fr _ _ _ _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; zlia]
            | idtac "WARNING: framed2 fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stableL ?Fr _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; in_some_tac]
            | idtac "WARNING: framedL fact dropped at store" a; clear H ]
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.
(* [comment removed for export] *)
Ltac zmem_transport M a bs ::=
  zwb_pre M a bs; zxfer_pre a bs;
  zmem_transport_loop_TBase M a bs;
  zxfer_post a; zwb_post a.

(* [comment removed for export] *)
Ltac zreattachL_extra HA Mo Mn ::=
  try match goal with
  | H : rom_ok Mo |- _ =>
      first [ let H' := fresh in
              pose proof (rom_ok_magreeL Mo Mn _ H HA ltac:(unfold ROM_LO, ROM_HI; disj_all_tac)) as H';
              clear H; rename H' into H
            | idtac "zreattachL: dropped rom_ok"; clear H ]
  end;
  try match goal with
  | H : i_frame ?cx Mo |- _ =>
      first [ apply (i_frame_magreeL cx Mo Mn _ HA) in H; [| icx_cbn; zlia | icx_cbn; zlia | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped i_frame"; clear H ]
  end;
  try match goal with
  | H : i_cst ?segs ?cx Mo |- _ =>
      first [ apply (i_cst_magreeL segs cx Mo Mn _ HA) in H;
              [| icx_cbn; zlia | icx_cbn; zlia | icx_cbn; zlia | icx_cbn; cbv [STATE_SIZE]; zlia
               | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped i_cst"; clear H ]
  end;
  try match goal with
  | H : i_hooks ?cx Mo |- _ =>
      first [ apply (i_hooks_magreeL cx Mo Mn _ HA) in H; [| icx_cbn; zlia | icx_cbn; zlia | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped i_hooks"; clear H ]
  end;
  try match goal with
  | H : st_at ?segs ?cx ?st Mo |- _ =>
      first [ apply (st_at_magreeL segs cx st Mo Mn _ HA) in H; [| icx_cbn; zlia | icx_cbn; cbv [STATE_SIZE]; zlia | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped st_at"; clear H ]
  end;
  try match goal with
  | H : st_rest ?segs ?cx ?st Mo |- _ =>
      first [ apply (st_rest_magreeL segs cx st Mo Mn _ HA) in H; [| icx_cbn; zlia | icx_cbn; cbv [STATE_SIZE]; zlia | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped st_rest"; clear H ]
  end;
  try match goal with
  | H : strm_at ?segs ?cx ?st Mo |- _ =>
      first [ apply (strm_at_magreeL segs cx st Mo Mn _ HA) in H;
              [| icx_cbn; zlia | icx_cbn; zlia | icx_cbn; zlia | icx_cbn; cbv [STATE_SIZE]; zlia | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped strm_at"; clear H ]
  end;
  try match goal with
  | H : s_ret ?cx ?st Mo |- _ =>
      first [ unfold s_ret in H; apply (mem_u64_magreeL1 _ Mo Mn _ _ _ HA) in H; [|solve [icx_cbn; zsideL]]; change (s_ret cx st Mn) in H
            | idtac "zreattachL: dropped s_ret"; clear H ]
  end;
  try match goal with
  | H : s_lo ?cx ?st Mo |- _ =>
      first [ apply (s_lo_magreeL cx st Mo Mn _ HA) in H; [| icx_cbn; zlia | icx_cbn; zlia | icx_cbn; disj_all_tac | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped s_lo"; clear H ]
  end;
  try match goal with
  | H : s_bk ?cx ?st Mo |- _ =>
      first [ apply (s_bk_magreeL cx st Mo Mn _ HA) in H; [| icx_cbn; zlia | icx_cbn; cbv [STATE_SIZE]; zlia | icx_cbn; disj_all_tac ]
            | idtac "zreattachL: dropped s_bk (callee footprint covers p+7164)"; clear H ]
  end;
  repeat match goal with
  | H : mem_arr ?k ?segs Mo ?base ?n ?f |- _ =>
      first [ apply (mem_arr_magreeL segs k Mo Mn _ base n f HA) in H; [| disj_all_tac ]
            | idtac "zreattachL: dropped mem_arr at" base; clear H ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac open_cx CX :=
  let CXl := fresh "CXl" in
  dand CX as (CXl & AL & SEP);
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_T] in CXl; destr_conj CXl.

(* [comment removed for export] *)
Ltac disj_all_tac ::= solve [ cbv [N_LENS N_CODES N_WORK STATE_SIZE WIN_SIZE ZS_SIZE FRA]; zconj_norm; repeat split; first [ exact I | zlia ] ].

(* [comment removed for export] *)
Ltac zkeysb := zkeys; cbv [ROMHI_T FR_INF FR_UW FR_IT FR_IF FR_AD] in *.

(* [comment removed for export] *)
Ltac zgetl_nil := repeat match goal with H : zget_l ?R [] ?k = _ |- _ => cbv beta iota delta [zget_l alookup] in H end.

(* [comment removed for export] *)
Ltac fp_cbv_in H := unfold fp_loop, fp_win, fp_lib in H; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE WIN_SIZE] in H.
Ltac fp_frame_init fp M :=
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M fp ltac:(unfold fp_loop, fp_win, fp_lib; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE WIN_SIZE]; ranges_ok_tac)) as HST;
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X fp) M) by (apply mpostL_refl);
  fp_cbv_in HST; fp_cbv_in HAG.
(* [comment removed for export] *)
Ltac fp_frame_from HP0 :=
  lazymatch type of HP0 with mpostL ?segs ?M0 ?M ?fp =>
    let HST := fresh "HST" in let HAG := fresh "HAG" in
    pose proof (mpostL_stable segs M0 fp ltac:(unfold fp_loop, fp_win, fp_lib; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE WIN_SIZE]; ranges_ok_tac)) as HST;
    change (framed (fun X => mpostL segs M0 X fp) M) in HP0; rename HP0 into HAG;
    fp_cbv_in HST; fp_cbv_in HAG
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section K.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).

(* [comment removed for export] *)
Definition k_mem (st : ist) (lf cf : Z -> Z) (M : mem) : Prop :=
  s_std cx fin M /\ st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\ s_ret cx st M /\ s_lo cx st M /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf /\
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) /\
  s_bk cx st M.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition KDISP (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> meas cx st < B -> s_regs_disp cx st R [] -> k_mem st lf cf M ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DISP (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition s_regs_redisp (st : ist) (R : tree Z) : Prop :=
  zget R kSP = c_u cx + -256 /\ zget R kGP = c_K cx kGP /\ zget R kTP = c_K cx kTP /\
  zget R kS0 = c_p cx /\ zget R kS1 = c_u cx /\ zget R kRA = 16209 /\
  zget R kS10 = c_q cx + t_cin st /\ zget R kS8 = c_n cx - t_cin st /\
  zget R kS3 = c_ob cx + t_cout st /\ zget R kS4 = t_hold st /\ zget R kS2 = t_bits st.
Definition KREDISP (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> meas cx st < B -> s_regs_redisp st R -> k_mem st lf cf M ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_REDISP (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition KREDISP_A1 (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> meas cx st < B -> s_regs_redisp st R -> zget R kA3 = c_u cx -> k_mem st lf cf M ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_REDISP_A1 (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition bad_of (st : ist) : ist :=
  IST BAD (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
(* [comment removed for export] *)
Definition KBADMSG_A0 (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx (bad_of st) lf cf -> meas cx (bad_of st) < B ->
    zget R kSP = c_u cx + -256 -> zget R kGP = c_K cx kGP -> zget R kTP = c_K cx kTP ->
    zget R kS0 = c_p cx -> zget R kS1 = c_u cx ->
    zget R kS10 = c_q cx + t_cin st -> zget R kS8 = c_n cx - t_cin st ->
    zget R kS3 = c_ob cx + t_cout st -> zget R kS4 = t_hold st -> zget R kS2 = t_bits st ->
    0 <= zget R kA0 < two64 -> k_mem st lf cf M ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_BADMSG_A0 (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition KBADMSG_A5 (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx (bad_of st) lf cf -> meas cx (bad_of st) < B ->
    s_fix cx R [] -> zget R kA4 = c_q cx + t_cin st -> zget R kA2 = c_n cx - t_cin st ->
    zget R kS3 = c_ob cx + t_cout st -> zget R kS4 = t_hold st -> zget R kS2 = t_bits st ->
    0 <= zget R kA5 < two64 -> k_mem st lf cf M ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_BADMSG_A5 (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition KBADMSG_A5B (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> meas cx st < B ->
    s_fix cx R [] -> zget R kA4 = c_q cx + t_cin st -> zget R kA2 = c_n cx - t_cin st ->
    zget R kS3 = c_ob cx + t_cout st -> zget R kS4 = t_hold st -> zget R kS2 = t_bits st ->
    k_mem st lf cf M ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_BADMSG_A5B (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition KBADMSG_A1 (B : Z) : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx (bad_of st) lf cf -> meas cx (bad_of st) < B ->
    zget R kSP = c_u cx + -256 -> zget R kGP = c_K cx kGP -> zget R kTP = c_K cx kTP ->
    zget R kS0 = c_p cx -> zget R kS1 = c_u cx -> zget R kRA = 16209 ->
    zget R kA7 = c_q cx + t_cin st -> zget R kS8 = c_n cx - t_cin st ->
    zget R kS3 = c_ob cx + t_cout st -> zget R kS4 = t_hold st -> zget R kS2 = t_bits st ->
    0 <= zget R kA1 < two64 -> k_mem st lf cf M ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_BADMSG_A1 (zupd R []) M MD) T.

(* [comment removed for export] *)
Definition KLEAVE : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (rv : Z) (lf cf : Z -> Z),
    sinv cx st lf cf -> s_regs_leave cx st rv R [] ->
    s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> s_lo cx st M -> s_bk cx st M ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition KLEAVE_LD : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> s_regs_leave_ld cx st R [] ->
    s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> s_ret cx st M -> s_lo cx st M -> s_bk cx st M ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition KLEAVE_LD2 : Prop :=
  forall (R : tree Z) (M : mem) (st : ist) (lf cf : Z -> Z),
    sinv cx st lf cf -> s_regs_leave_ld2 cx st R [] ->
    s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> s_ret cx st M -> s_lo cx st M -> s_bk cx st M ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD2 (zupd R []) M MD) T.
(* [comment removed for export] *)
Definition KRET : Prop :=
  forall (R : tree Z) (M : mem) (rc m : Z),
    rc mod two64 <> 0 -> s_regs_ret cx rc R [] -> s_std cx fin M ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 8) m -> reach m ->      (* [comment removed for export] *)
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_RET (zupd R []) M MD) T.
End K.

Ltac open_kmem H := let STD := ident:(STD) in let SAT := ident:(SAT) in let SRET := ident:(SRET) in let SLO := ident:(SLO) in let Hlens := ident:(Hlens) in let Hcodes := ident:(Hcodes) in let HP0 := ident:(HP0) in let SBK := ident:(SBK) in (first [ dand H as (STD & SAT & SRET & SLO & Hlens & Hcodes & HP0 & SBK)
        | (* [comment removed for export] *)
          let S := fresh "SBK" in dand H as (STD & SAT & SRET & SLO & Hlens & Hcodes & HP0 & S) ]).

(* [comment removed for export] *)
Ltac sbk_modes := icx_cbn; cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                                TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC];
                  first [ discriminate | lia_std ].
Ltac sbk :=
  first [ assumption
        | match goal with H : s_bk _ _ ?M |- s_bk _ _ ?M =>
            first [ apply (s_bk_same _ _ _ _ H); solve [icx_cbn; first [reflexivity | assumption | lia_std]]
                  | apply (s_bk_other _ _ _ _ H); solve [sbk_modes] ] end
        | eapply s_bk_free;
          [ icx_cbn; cbv [STATE_SIZE];
            first [ assumption | match goal with S : s_std _ _ _ |- _ => exact (proj1 (proj2 (proj2 S))) end ]
          | icx_cbn; lia_std | icx_cbn; cbv [STATE_SIZE]; lia_std | solve [sbk_modes] | solve [sbk_modes] ] ].

(* [comment removed for export] *)
Definition KALL {RCa1 : RunCtx}  (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem) (B : Z) : Prop :=
  KDISP cx fin MD T M0 B /\ KREDISP cx fin MD T M0 B /\ KREDISP_A1 cx fin MD T M0 B /\
  KBADMSG_A0 cx fin MD T M0 B /\ KBADMSG_A5 cx fin MD T M0 B /\ KBADMSG_A5B cx fin MD T M0 B /\ KBADMSG_A1 cx fin MD T M0 B /\
  KLEAVE cx fin MD T M0 /\ KLEAVE_LD cx fin MD T M0 /\ KLEAVE_LD2 cx fin MD T M0 /\ KRET cx fin MD T M0.
Ltac open_K H := dand H as (KD & KRD & KRD1 & KB0 & KB5 & KB5B & KB1 & KL & KLL & KLL2 & KRT).

Lemma KALL_mono {RCa1 : RunCtx}  : forall cx fin MD T M0 B B', B' <= B -> KALL cx fin MD T M0 B -> KALL cx fin MD T M0 B'.
Proof.
  intros cx fin MD T M0 B B' HB K. open_K K.
  unfold KALL, KDISP, KREDISP, KREDISP_A1, KBADMSG_A0, KBADMSG_A5, KBADMSG_A5B, KBADMSG_A1 in *.
  split_conj; try assumption; intros; first [eapply KD | eapply KRD | eapply KRD1 | eapply KB0 | eapply KB5 | eapply KB5B | eapply KB1];
    try eassumption; lia_std.
Qed.

(* [comment removed for export] *)
Definition arm_stmt {RCa1 : RunCtx}  (L X : Z) : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = X -> sinv cx st lf cf ->
    s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L (zupd Rb l) M MD) T.

(* [comment removed for export] *)
Definition arm_stmt_ob {RCa1 : RunCtx}  (L X : Z) : Prop :=
  forall (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem)
         (Rb : tree Z) (l : list (positive * Z)) (M : mem) (st : ist) (lf cf : Z -> Z),
    ctx_ok ROMHI_T cx -> c_ob cx + c_osz cx <= c_u cx - FRA ->
    m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
    t_mode st = X -> sinv cx st lf cf ->
    s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
    KALL cx fin MD T M0 (meas cx st) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L (zupd Rb l) M MD) T.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memcpy_spec_t {RCa1 : RunCtx}  : Prop := memcpy_spec_at (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMCPY.
Definition itable_spec_t {RCa1 : RunCtx}  : Prop := itable_spec_at (run_segments R_segs rc_inp rc_sp rc_mb) L_ITABLE FR_IT.
Definition ifast_spec_t {RCa1 : RunCtx}  : Prop := ifast_spec_at (run_segments R_segs rc_inp rc_sp rc_mb) L_IFAST FR_IF.
(* [comment removed for export] *)
Definition adler32_spec_t {RCa1 : RunCtx}  : Prop := adler32_spec_at (run_segments R_segs rc_inp rc_sp rc_mb) A_ADLER32 FR_AD rom_ok.
(* [comment removed for export] *)
Definition adler32_null_spec_t {RCa1 : RunCtx}  : Prop := adler32_nullF_spec_at (run_segments R_segs rc_inp rc_sp rc_mb) A_ADLER32 FR_AD.
