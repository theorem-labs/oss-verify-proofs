(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge Image Mem SysStep ITree Nodes FP.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RF_fi_iface RF_fi_small RF_fi_gfha RF_fi_gfha2 RF_fi_wrap RF_fi_ffsi RF_fi_dbound RF_fi_fds.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Malloc Monad Stdio Harness Prog.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma errno_lit : bv_unsigned (Z_to_bv 64 RATP) + -164 = RERRNO.
Proof. unfold RATP, RERRNO. Local Ltac2 Set LiaHints.tbl := fun () => "0010=15717690727.1000001S".
rewrite unsigned_lit by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rheap_pres_of_munch : forall LB SP W m m',
  munch W m m' -> wmono usegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) ->
  rheap_pres LB SP m m'.
Proof.
  intros LB SP W m m' MU WM OUT a Ha Hc. split.
  - apply MU. unfold wa. Local Ltac2 Set LiaHints.tbl := fun () => "0010>56765666539.12000004S2Ha".
rewrite unsigned_lit by lia. apply OUT; assumption.
  - intros Hv. apply WM. exact Hv.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma RHEAP_stack_frame : forall s LB m m' W,
  RHEAP s LB m -> munch W m m' -> wmono usegs m m' ->
  Forall (fun iv => ATOP <= fst iv) W -> RHEAP s LB m'.
Proof.
  intros s LB m m' W HP MU WM FW. eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
  eapply Forall_impl; [| exact FW]. intros iv H. left. exact H.
Qed.

#[using="Type"] Lemma rauxv_ok_stack_frame : forall m m' B W,
  rauxv_ok m B -> munch W m m' -> wmono usegs m m' ->
  Forall (fun iv => ATOP <= fst iv /\ snd iv <= B) W -> rauxv_ok m' B.
Proof.
  intros m m' B W AUX MU WM FW. eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
  eapply Forall_impl; [| exact FW]. intros [lo hi] [H1 H2]. cbn [fst snd] in *. unfold RAUXV_CELL in *. atop_facts. Local Ltac2 Set LiaHints.tbl := fun () => "0010=8514744513.1400000=S2H12H25ATOPR".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma land_m1_lit : forall D, 0 <= D < 2^64 -> Z.land 18446744073709551615 D = D.
Proof.
  intros D HD. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "0020=35497647514.38548822950.3 000001005SS2HD".
rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ltoi_post (ra : word) (T : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m0 : fmem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : fmem),
    ms' = MS (mkR ra (Z_to_bv 64 T) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, T)] m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ stk usegs m' lo T.

(* [comment removed for export] *)
Ltac leaf_call G PL PLR :=
  zstep;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evt_cut; [ eapply G; first [ split; [exact PL| exact PLR] | eassumption | lia | reflexivity ] | ]; post_call usegs mc end;
  clear G; try rename MI0 into MI.

#[using="Type"] Lemma ltoi_main : forall (ra : word) (T : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S' : Z) (bl : list Z) (lo : Z) (j0 zj : list byte),
  buf_at m0 S' bl -> (0 < S' \/ zlen bl = 0) -> zlen bl < 2^26 -> S' + zlen bl < 2^63 -> S' + zlen bl <= lo ->
  stk usegs m0 lo (T + -80) -> lo <= T - 16384 -> T < 2^64 -> T mod 16 = 0 ->
  rw_cells usegs m0 (T + -80) [CB 8 j0; CB 48 zj; C8 s1; C8 s0; C8 ra] ->
  mem_inv usegs m0 ->
  evt usegs (ltoi_post ra T gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0)
    (MS (mkR ra (Z_to_bv 64 (T + -80)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (zlen bl)) (Z_to_bv 64 S') x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12cac) fc None m0 (seg_rom usegs)).
Proof.
  intros until zj. intros BUF S0 NB SN SLO ST LOS TH T16 FR MI.
  pose proof (proj1 BUF) as PL. pose proof (proj2 BUF) as PLR.
  pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
  assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = zlen bl) by (rewrite length_map; reflexivity).
  assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(lo, T)] m0) as MU. pose proof (wmono_refl usegs m0) as WM.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  (* [comment removed for export] *)
  zstep. zstep. pose proof gfcs_proof as G. unfold gfcs_stmt, wrap_stmt, leaf_post, WRAP_FRAME, PFI_GFCS in G. Local Ltac2 Set LiaHints.tbl := fun () => "01_0?11799489569.12311799489569.15311799489569.93 11801586693.10811801586693.13811801586693.77 12428150072.18212428150072.20113494921898.16013494921898.17915920882553.18315920882553.20216708599058.13817761707061.10317761707061.11817761707061.13317761707061.16017761707061.17917761707061.57 17761707061.73 17761707061.88 18488685590.17922700267513.10922700267513.12422700267513.13922700267513.15422700267513.78 22700267513.94 24822356032.18324822356032.20225076071819.18225076071819.18325076071819.20125076071819.20225144511712.10325144511712.11825144511712.13325144511712.57 25144511712.73 25144511712.88 25656252822.19825804454294.10326921664681.2022856735956.159 2857134066.197 28773085302.12328773085302.15328773085302.93 28775182418.10828775182418.13828775182418.77 30548993194.88 32188822546.77 32190919734.12332190919734.93 32202844500.15932203496050.19733735042735.13334058503850.10334058503850.57 34058503850.73 3536802582.103 3536802582.118 3536802582.133 3536802582.57  3536802582.73  3536802582.88  35510343002.16035510343002.17936068125610.13336284089650.88 36547323049.20436569086895.16036569086895.17937060208950.15338127594800.15738672688831.10338672688831.11838672688831.13338672688831.16038672688831.17938672688831.57 38672688831.73 38672688831.88 38768013667.16038768013667.17940178163625.20440570239482.19544484923210.10844484923210.13844484923210.77 44487020398.12344487020398.15344487020398.93 45362656306.11847397207471.88 49848632626.14850313592797.19455245984431.11856633542570.11857383728658.10857622410744.18357622410744.2025972701590.133 6212979998.182 6212979998.201 62550303126.73 63887271855.10363887271855.57 63887271855.73 65211159353.15300000400800<00@00D00H00I00J00R00Z00[00\00]00d00k01201901@01G01N01U01Y01c01m02702A02K02U02f03703;03?03C03D03E03F03G03H03I03J03N03R03V03Z03^03o04@04Q04b05305D05L05M05N05O05S05W05c05k06306;06<06=06>06?06@06A06E06I06Q06U06Y06e07107207607=07D07K07R07Y07`07g07n08:08F08J08R08S08T08U08V08W08X08\08h08l09009<09D09E09O09Y09]09a09e09i0:50:A0:M0:QS2FBS2FBS2FBS2FBS2FBS2FBFFS3LOS2FBS3LOS2FBFFFS2NB2FBS2NB2FBS2NB2FBS2NB2FBS2NB2FBS2NB2FBS2NB2FBS2NB2FBS2FBS3LOS2FB1HS3LOS2FB1HS3LOS2FB1HS3LOS2FB1HS3LOS2FB1HS3LOS2FB1HS3SLO3LOS4LENB2FBS3SLO3LOS4LENB2FBS2FBS2FBS2FBFFFFFFFS2FBS2FBS2FBS2FBS2FBS3SLO3LOS4LENB2FBS3SLO3LOS4LENB2FBS3SLO3LOS4LENB2FBS3SLO3LOS4LENB2FBS3SLO3LOS4LENB2FBS3SLO3LOS4LENB2FBS3LOS2FBFFFS2FBS2FBS3SLO3LOS2FBS3LOS2FBS3LOS2FBS3LOS2FBFFFFFFS2FBS2FBS3LOS2FBS2FBS2FBS3SLO3LOS2FBS3SLO3LOS2FBFS2FBS2TH2FBS2TH2FBS2TH2FBS2TH2FBS2TH2FBS2TH2FBS2TH2FBS2TH2FBS3SLO3LOS2FBS3SLO3LOS2FBS2FBS3LOS2FBFFFFFFS2FBS3SLO3LOS2FBS2FBS2FBS3SLO3LOS2FBS3LOS2FBFS3LOS2FB1HS3LOS2FB1HS2FBS2FBS2FBS2FBS3SLO3LOS2FBS3SLO3LOS2FBS3SLO3LOS2FBS2FB".
leaf_call G PL PLR.
  (* [comment removed for export] *)
  zstep. zstep. pose proof gds_proof as G. unfold gds_stmt, wrap_stmt, leaf_post, WRAP_FRAME, PFI_GDS in G. leaf_call G PL PLR.
  (* [comment removed for export] *)
  zstep. zstep. pose proof ffcs_proof as G. unfold ffcs_stmt, leaf_stmt, leaf_post, FFCS_DEPTH, PFI_FFCS in G. leaf_call G PL PLR.
  (* [comment removed for export] *)
  zstep. zstep. pose proof gdid_proof as G. unfold gdid_stmt, wrap_stmt, leaf_post, WRAP_FRAME, PFI_GDID in G. leaf_call G PL PLR.
  (* [comment removed for export] *)
  zstep. zstep. pose proof fds_proof as G. unfold fds_stmt, leaf_stmt, leaf_post, FDS_DEPTH, PFI_FDS in G. leaf_call G PL PLR.
  (* [comment removed for export] *)
  zstep. zstep. pose proof dbound_proof as G. unfold dbound_stmt, leaf_stmt, leaf_post, DBOUND_DEPTH, PFI_DBOUND in G. leaf_call G PL PLR.
  (* [comment removed for export] *)
  zstep. zstep. pose proof fhsize_proof as G. unfold fhsize_stmt, fhsize_post, PFI_FHSIZE in G.
  zstep. eapply evt_cut; [ eapply G; [ split; [exact PL| exact PLR] | assumption | assumption | reflexivity | reflexivity ] | ].
  clear G. intros ms' PO7. destruct PO7 as (r7 & ? & ? & ? & ? & ? & ? & ->).
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
  (* [comment removed for export] *)
  zstep. zstep. pose proof isframe_proof as G. unfold isframe_stmt, isframe_post, PFI_ISFRAME in G.
  zstep. eapply evt_cut; [ eapply G; [ split; [exact PL| exact PLR] | assumption | assumption | reflexivity | reflexivity ] | ].
  clear G. intros ms' PO8. destruct PO8 as (r8 & ? & ? & ? & ->).
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
  (* [comment removed for export] *)
  zstep. zstep. zstep. (* [comment removed for export] *)
  lazymatch goal with FRx : rw_cells _ ?m1 (T + -80) [?c0; ?cz; ?c1; ?c2; ?c3] |- _ =>
    apply (proj1 (rw_cells_app m1 _ [c0] [cz; c1; c2; c3])) in FRx; destruct FRx as [F0 FZ]; cbn [cells_size csize Nat.add] in FZ;
    apply (proj1 (rw_cells_app m1 _ [cz] [c1; c2; c3])) in FZ; destruct FZ as [FZ Fhi]; cbn [cells_size csize Nat.add] in Fhi end.
  replace (T + -80 + Z.of_nat 8) with (T + -72) in FZ, Fhi by lia.
  replace (T + -72 + Z.of_nat 48) with (T + -24) in Fhi by lia.
  pose proof gfh_proof as G. unfold gfh_stmt, gfha_stmt_at, gfha_post, GFHA_FRAME, PFI_GFH in G.
  zstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evt_cut; [ eapply G; [ split; [exact PL| exact PLR] | lia | exact FZ | lia | eassumption | lia | lia | lia | lia | lia | assumption | exact I
                 | f_equal; lia | reflexivity | reflexivity ] | ]; post_call usegs mc end.
  clear G. try rename MI0 into MI.
  (* [comment removed for export] *)
  lazymatch goal with PCx : rw_cells _ ?m2 (T + -72) [CB 24 _; CB 4 _; CB 20 _] |- _ =>
    destruct (rw_cells_forget usegs _ _ _ PCx) as [zj2 FZ]; clear PCx; cbn [cells_size csize Nat.add] in FZ end.
  try match goal with RF : _ mod _ = 0 -> exists h, _ |- _ => clear RF end.
  zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  pose proof gfha_proof as G. unfold gfha_stmt, gfha_stmt_at, gfha_post, GFHA_FRAME, PFI_GFHA in G.
  zstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evt_cut; [ eapply G; [ split; [exact PL| exact PLR] | lia | exact FZ | lia | eassumption | lia | lia | lia | lia | lia | assumption | reflexivity
                 | f_equal; lia | reflexivity | reflexivity ] | ]; post_call usegs mc end.
  clear G. try rename MI0 into MI.
  (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  lazymatch goal with PCx : rw_cells _ ?m2 (T + -72) ?cz, Fhix : rw_cells _ _ (T + -24) ?hi, F0x : rw_cells _ _ (T + -80) [?c0] |- _ =>
    assert (FR : rw_cells usegs m2 (T + -80) ([c0] ++ (cz ++ hi)))
      by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact F0x|]; cbn [cells_size csize Nat.add];
          replace (T + -80 + Z.of_nat 8) with (T + -72) by lia;
          apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact PCx|]; cbn [cells_size csize Nat.add];
          match goal with |- rw_cells _ _ ?a _ => replace a with (T + -24) by lia end; exact Fhix);
    clear PCx Fhix F0x; cbn [app] in FR end.
  zstep. zstep. zstep. (* [comment removed for export] *)
  lazymatch goal with STx : stk _ _ lo _ |- _ => release_frame FR STx T end.
  zstep. zstep. (* [comment removed for export] *)
  finish. all: try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Theorem fuzz_one_final : fuzz_one_stmt.
Proof.
  unfold fuzz_one_stmt. intros until errv. intros HP PAY PAYB PAYR D16 D0 DTOP SZ HC SE AUX SPB ST LOA LOS ERR MI FC TP SP16 A0 A1.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold HARNESS_STACK in LOS. atop_facts.
  unfold wz in *. subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
  unfold zlength in *.
  assert (LENP : Z.of_nat (length (map (Z_to_bv 8) payload)) = zlen payload) by (rewrite length_map; reflexivity).
  assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold Prog.fuzz_one, Harness.fuzz_one. cbv zeta.
  apply implM_ret.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  clear HC SE.
  Local Ltac2 Set LiaHints.tbl := fun () => "00W0>11355099880.7111355099880.7415045700061.6616083456461.7716451336353.6617452146992.6917991351565.9222706553108.9522706661829.9924767406629.6829034161356.923981044591.92 40374333670.6840986768000.7140986768000.7442548627563.7143059266230.6643779659719.7144977136295.7446110623150.6846417205840.7146887021955.7447663274663.7449705053714.7149705053714.7452074235541.835300226131.71 5300226131.74 5490262775.66 5896867971.71 61486757361.9261994440323.7465494693853.6666173797565.7167541566890.7167541566890.7467965490855.718542205841.83 8544726733.69 00000B00T00U00Y00Z00^00c01801C01G01P01[01\02202H02M02R02W02X02\02k02l02m03503=03>03B03F03P03Q03R03S03d03h04004804904M04aS3LOA3LOS5ATOPR2HBS3LOA3LOS5ATOPR2HBSS2SZSS2NZS3LOAS2Hc2D03LOA3RSP5ATOPRS3LOA2H02R4S2HiS3SPB3LOAS3LOA5ATOPRSS4DTOP3LOA3LOS4LENP2HBS4DTOP3LOA3LOS4LENP2HBS3LOSS3LOSS3RSPSS2Z0S4DTOP5ATOPR2SDSSS3RSP2HBS3RSP2HBFS2HBS2HBS4DTOP3LOASSSS2D03LOA5ATOPR2Z0S2SZS3LOS2HBS3LOS2HBSS2D04DTOP5ATOPR4LENPS2D04DTOP5ATOPR4LENP".
carve_frame 80%nat ST.
  apply (rw_cells_split_CB usegs m _ [] 80 junk [] [8; 48; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  subst a0 a1. unfold PFUZZ_ENTRY.
  do 4 zstep. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (CASES : exists S', (zlen payload = 0 /\ S' = 0 \/ zlen payload <> 0 /\ S' = D)
                            /\ (forall mm, bytes_at usegs mm D (map (Z_to_bv 8) payload) -> buf_at mm S' payload)
                            /\ S' + zlen payload <= lo /\ S' <= D).
  { destruct (Z.eq_dec (zlen payload) 0) as [Z0|NZ].
    - exists 0. split; [left; split; [exact Z0| reflexivity]|]. split; [| lia]. intros mm _.
      assert (payload = []) as -> by (destruct payload; [reflexivity| cbn in Z0; lia]).
      split; [| constructor]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - exists D. split; [right; split; [exact NZ| reflexivity]|]. split; [| lia]. intros mm P. split; assumption. }
  destruct CASES as (S' & CS & BUFm & SLO & SD).
  zstep. zstep. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS (TNode (TNode _ (Some _) (TNode (TNode _ (Some ?v9) _) (Some _) _)) None _) _ _ _ _ _ _) =>
    replace v9 with (Z_to_bv 64 S') end.
  2: { (* [comment removed for export] *)
       destruct CS as [[Z0 ->]|[NZ ->]].
       - rewrite Z0. change (Z.b2z (0 <? 1) + -1) with 0. rewrite !Z.land_0_l. reflexivity.
       - replace (zlen payload <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
         change (Z.land (Z.b2z false + -1) 18446744073709551615) with 18446744073709551615.
         rewrite land_m1_lit by (atop_facts; lia). reflexivity. }
  lazymatch goal with P : bytes_at usegs _ D (map (Z_to_bv 8) payload) |- _ => pose proof (BUFm _ P) as BUF' end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
  lazymatch type of FR with rw_cells _ _ _ [CB 8 ?j0; CB 48 ?zj; _; _; _] =>
    eapply evt_cut; [ eapply (ltoi_main ra (bv_unsigned sp) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 S' payload lo j0 zj);
      [ exact BUF' | lia | lia | atop_facts; lia | exact SLO | exact ST | lia | lia | exact SP16 | exact FR | exact MI ] | ] end end.
  intros ms' PO. destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU2 & WM2 & MI2 & ST2).
  apply evt_done. unfold fuzz_one_post.
  assert (MU3 : munch [(lo, bv_unsigned sp)] m m') by (eapply munch_trans; [exact MU| exact MU2]).
  assert (WM3 : wmono usegs m m') by (eapply wmono_trans; [exact WM| exact WM2]).
  rewrite Z_to_bv_bv_unsigned.
  do 14 eexists. exists F, fc, m', errv. split; [reflexivity|].
  split; [lia|]. split; [exact MI2|]. split; [exact FC|].
  split; [exact ST2|].
  split.
  { (* [comment removed for export] *) rewrite errno_lit. unfold RERRNO.
    match goal with E : rw_cells _ _ 188300 _ |- _ => eapply (rw_cells_transport usegs _ _ _ _ _ E MU2 WM2) end.
    cbn [disjoint_from cells_size csize Nat.add]. atop_facts. lia. }
  split; [eapply rauxv_ok_stack_frame; [exact AUX| exact MU3| exact WM3| constructor; [cbn; atop_facts; lia| constructor]]|].
  split.
  { eapply rheap_pres_of_munch; [exact MU3| exact WM3|]. intros a Ha Hc. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|].
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ _ HP Hb) as (_ & _ & _ & R4 & _). destruct Hr. atop_facts. lia. }
  split; [eapply RHEAP_stack_frame; [exact HP| exact MU3| exact WM3| constructor; [cbn; atop_facts; lia| constructor]]|].
  reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
