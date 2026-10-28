(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass SegRw.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_iface D_defs R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_depot_defs R_fs_defs R_glue_defs R_sec_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame TopA_iodefs GDesc LibSh RT_main_shape RT_main_img.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CONSTS_LIT_S : list (saddr * list scell) :=
  [ (SA LB_lit (i_spacebeg + 8), [SC_lit 8 0xffffffff]);
    (SA LB_lit i_premapped, [SC_lit 1 0]);
    (SA LB_lit 0x5a9218, [SC_lit 8 0x701ae0]);
    (SA LB_lit 0x5a9228, [SC_lit 8 0x703b68]);
    (SA LB_lit 0x701ae0, [SC_lit 8 4096]);
    (SA LB_lit 0x703bf8, [SC_lit 8 0]);
    (SA LB_lit 0x703c6c, [SC_lit 1 0]);
    (SA LB_lit g_tsd_key_inited, [SC_lit 1 1]);
    (SA LB_lit g_tsd_key, [SC_lit 4 0]);
    (SA LB_lit pth_tsd, [SC_lit 8 g_pthread_tsd_main]);
    (SA LB_lit 0x5a9238, [SC_lit 8 0x672038; SC_lit 8 0x672d28; SC_lit 8 0x672d30; SC_lit 8 0x672d20]);
    (SA LB_lit 0x672038, [SC_lit 8 SHB]);
    (SA LB_lit 0x672d20, [SC_lit 8 kHighMemEnd; SC_lit 8 0; SC_lit 8 0]);
    (SA LB_lit g_got_real_memset, [SC_lit 8 g_real_memset]);
    (SA LB_lit g_real_memset, [SC_lit 8 musl_memset_entry]);
    (SA LB_lit g_can_poison, [SC_lit 1 1]);
    (SA LB_lit g_cf_clear_shadow_mmap_threshold, [SC_lit 8 0xffffffffffffffff]);
    (SA LB_lit 0x672d3c, [SC_lit 4 30]);
    (SA LB_lit 0x66f7f8, [SC_lit 8 (2 ^ 40)]);
    (SA LB_lit 0x66f800, [SC_lit 2 16; SC_lit 2 2048]);
    (SA LB_lit 0x6f42a2, [SC_lit 1 0]);
    (SA LB_lit 0x703b8a, [SC_lit 1 1]);
    (SA LB_lit 0x5a9230, [SC_lit 8 0x66f838]);
    (SA LB_lit (0x66f838 + 44), [SC_lit 4 4096]);
    (SA LB_lit (0x66f838 + 52), [SC_lit 4 190]);
    (SA LB_lit (0x66f838 + 85), [SC_lit 1 1]);
    (SA LB_lit (0xba93f0 + 32), [SC_lit 4 0]);
    (SA LB_lit 0x5a9eb0, [SC_lit 8 32]);
    (SA LB_lit 0x703b00, [SC_lit 8 0]);
    (SA LB_lit 0x67189c, [SC_lit 1 1]);
    (SA LB_lit 0x703b08, [SC_lit 8 0]);
    (SA LB_lit 0x66ecf0, [SC_lit 8 0x10000000; SC_lit 8 0xE666661; SC_lit 8 0x100000]);
    (SA LB_lit 0x66f868, [SC_lit 4 0]);
    (SA LB_lit 0x5a9278, [SC_lit 8 1]);
    (SA LB_lit 0x703c43, [SC_lit 1 1]);
    (SA LB_lit 0x703c5c, [SC_lit 1 1]);
    (SA LB_lit 0x5ab1e0, [SC_lit 8 0xbc9430]);
    (SA LB_lit 0xbc96b0, [SC_lit 8 4096]) ].
(* [comment removed for export] *)
Definition CONSTS_RO_S : list (saddr * list scell) :=
  [ (SA LB_lit g_GOT_shadow_offset_cell, [SC_lit 8 g_shadow_memory_dynamic_address]);
    (SA LB_lit g_shadow_memory_dynamic_address, [SC_lit 8 SHB]);
    (SA LB_lit g_GOT_detect_uar, [SC_lit 8 g_detect_stack_use_after_return]);
    (SA LB_lit g_detect_stack_use_after_return, [SC_lit 4 1]);
    (SA LB_lit 0x703c5d, [SC_lit 1 0]);
    (SA LB_lit 0x703c64, [SC_lit 1 1]);
    (SA LB_lit 0x5a9230, [SC_lit 8 0x66f838]);
    (SA LB_lit 0x5a9260, [SC_lit 8 0x5ac4a8]);
    (SA LB_lit 0x5ac4a8, [SC_lit 8 0x52b0ac]);
    (SA LB_lit 0x66f855, [SC_lit 1 1]);
    (SA LB_lit 0x703b8a, [SC_lit 1 1]);
    (SA LB_lit 0x5ab1e0, [SC_lit 8 0xbc9430]);
    (SA LB_lit 0x5ab1e0, [SC_lit 8 0xbc9430]);
    (SA LB_lit 0x5a9dc0, [SC_lit 8 0x672d19]);
    (SA LB_lit 0x672d19, [SC_lit 1 1]);
    (SA LB_lit 0x5ac4b0, [SC_lit 8 0x52b4e0]);
    (SA LB_lit 0x5ac2d0, [SC_lit 8 0x52afb0]);
    (SA LB_lit 0x5ac458, [SC_lit 8 0x52bc80]);
    (SA LB_lit 0x5ac288, [SC_lit 8 0x52b9dc]);
    (SA LB_lit 0x703c63, [SC_lit 1 1]);
    (* [comment removed for export] *)
    (SA LB_lit 0x5ac450, [SC_lit 8 0x52b730]) ].
(* [comment removed for export] *)
Definition TGA_LIT_S : list (saddr * list scell) :=
  [ (SA LB_lit 0x672d18, [SC_lit 1 1]);
    (SA LB_lit g_real_tls_get_addr, [SC_lit 8 musl_tls_get_addr_entry]);
    (SA LB_lit g_dtv_ptr, [SC_lit 8 g_dtv]);
    (SA LB_lit g_dtv1, [SC_lit 8 dtv1_val]);
    (SA LB_lit R_tlsgetaddr.g_got_common_flags, [SC_lit 8 g_common_flags]);
    (SA LB_lit g_intercept_tls_get_addr, [SC_lit 1 1]);
    (SA LB_lit g_got_verbosity, [SC_lit 8 g_current_verbosity]);
    (SA LB_lit g_current_verbosity, [SC_lit 4 0]);
    (SA LB_lit g_tls_index, [SC_lit 8 1; SC_lit 8 0xfffffffffffff800]);
    (SA LB_lit g_got_dtls_off, [SC_lit 8 0x18]) ].

(* [comment removed for export] *)
Definition scell_of (c : cell) (v : Z) : scell := match c with C8 _ => SC_lit 8 v | C4 _ => SC_lit 4 v | C2 _ => SC_lit 2 v | C1 _ => SC_lit 1 v | CB n _ => SC_any n end.
Definition IO_RW_S : list (saddr * list scell) :=
  [ (SA LB_lit 0x5ac2e0, [SC_lit 8 0x5323d4; SC_lit 8 0x526710; SC_lit 8 0x526b70]); (SA LB_lit 0x66f8f0, [SC_lit 8 0]) ].
Definition IO_RO_S : list (saddr * list scell) :=
  [ (SA LB_lit 0x533428, [SC_lit 8 0x1f43d0; SC_lit 8 0x19ab8c; SC_lit 8 0x1f4400]); (SA LB_lit 0x5a9128, [SC_lit 8 0x5af428]);
    (SA LB_lit 0x5a9208, [SC_lit 8 0x51fb10; SC_lit 8 0]); (SA LB_lit 0x5a9eb8, [SC_lit 8 0x5a9128; SC_lit 8 0x1f40ec]);
    (SA LB_lit 0x5ab1c8, [SC_lit 8 0x5af720; SC_lit 8 0x66e960]); (SA LB_lit 0x5ab210, [SC_lit 8 0x533440; SC_lit 8 0x533428]);
    (SA LB_lit 0x5ac280, [SC_lit 8 0x5ac280]); (SA LB_lit 0x5ac318, [SC_lit 8 0x529f48; SC_lit 8 0x526dec; SC_lit 8 0x529f68]);
    (SA LB_lit 0x66f850, [SC_lit 4 1]); (SA LB_lit 0x703bbc, [SC_lit 1 1]); (SA LB_lit 0x703ee0, [SC_lit 1 0]) ].

(* [comment removed for export] *)
Definition CONSTS_SYM_S : list (saddr * list scell) :=
  [ (SA LB_lit i_spacebeg, [SC_ptr (SA LB_SB 0)]); (SA LB_lit i_regioninfo, [SC_ptr (SA LB_SB (2 ^ 37))]);
    (SA LB_lit g_pthread_tsd_main, [SC_ptr (SA LB_TCX 0)]); (SA LB_TCX 0x98, [SC_ptr (SA LB_T 0)]);
    (SA LB_T off_t_stack_top, [SC_ptr (SA LB_top 0)]); (SA LB_T (off_t_stack_top + 8), [SC_ptr (SA LB_top (-0x800000))]);
    (SA LB_T off_t_stack_switching, [SC_lit 1 0]); (SA LB_T 0xc60, [SC_lit 1 0]); (SA LB_TCX 8, [SC_lit 4 0]);
    (SA LB_T 0, [SC_ptr (SA LB_TCX 0)]) ].

(* [comment removed for export] *)
Definition ZERO_LIT_S : list (saddr * list scell) :=
  [ (SA LB_lit i_sec_chunks, [SC_ptr (SA LB_PAB 0)]); (SA LB_lit i_sec_nres, [SC_lit 8 0; SC_lit 8 0]); (SA LB_lit i_sec_mutex, [SC_lit 1 0]);
    (SA LB_lit (i_sec_mutex + 1), [SC_bytes [0; 0; 0]]);
    (SA LB_lit i_q_global, [SC_lit 8 0; SC_lit 8 0; SC_lit 8 0; SC_lit 8 0]); (SA LB_lit i_q_cmutex, [SC_lit 1 0; SC_lit 1 0; SC_lit 2 0]);
    (SA LB_lit i_sec_page, [SC_lit 8 4096]); (SA LB_lit i_sec_range, [SC_ptr (SA LB_PAB 0)]);
    (SA LB_lit i_sec_sorted, [SC_bytes (repeat 0 40)]); (SA LB_lit i_sec_bylog, [SC_bytes (repeat 0 512)]);
    (SA LB_lit i_gstat_alloc, [SC_lit 8 0; SC_lit 8 0]); (SA LB_lit 0x5a9220, [SC_lit 8 0x5ac4e8]); (SA LB_lit 0x5ac4e8, [SC_lit 8 sec_name]);
    (SA LB_lit g_ia_word, [SC_lit 4 0]); (SA LB_lit IAP, [SC_lit 1 0]); (SA LB_lit (IAP + 0x81008), [SC_bytes (repeat 0 40)]) ].

(* [comment removed for export] *)
Definition FS_DEP_S : list (saddr * list scell) :=
  [ (SA LB_FSB 0x58, [SC_lit 8 20; SC_lit 1 0]); (SA LB_lit tpA, [SC_ptr (SA LB_FSB 0)]);
    (SA LB_lit g_tls_dtls, [SC_ptr (SA LB_DTV 0)]); (SA LB_DTV 24, [SC_lit 8 0xba93f0]); (SA LB_T 48, [SC_lit 8 0xba9b28; SC_lit 8 0xba9c14]);
    (SA LB_lit d_nuniq, [SC_lit 4 1]); (SA LB_lit d_map1, [SC_ptr (SA LB_DNB 0)]); (SA LB_DNB 24, [SC_lit 4 0; SC_lit 4 1]);
    (SA LB_lit s_total, [SC_num 8 LN_f0]); (SA LB_lit s_data0, [SC_ptr (SA LB_SSB 0)]); (SA LB_lit s_stored0, [SC_num 4 LN_f0]) ].

Definition MAIN_RW : list (saddr * list scell) := CONSTS_LIT_S ++ TGA_LIT_S ++ IO_RW_S ++ CONSTS_SYM_S ++ ZERO_LIT_S ++ FS_DEP_S.
Definition MAIN_RO : list (saddr * list scell) := CONSTS_RO_S ++ IO_RO_S.

(* [comment removed for export] *)
Definition sh_zero_of (r : Z * Z) : saddr * Z := (SAsh LB_lit (fst r) 0, (snd r - 1) / 8 - fst r / 8 + 1).

Definition MAIN_ZERO : list (saddr * Z) :=
  [ (SA LB_SB (2 ^ 37 + 128), 128 * 31);          (* [comment removed for export] *)
    (SA LB_T 0x50, 0xc60 - 0x50);                 (* [comment removed for export] *)
    (SA LB_T 2768, 400);
    (SA LB_FSB 0, 0x58); (SA LB_FSB 0x1000, 0xb08000); (SAsh LB_FSB 0 0x1200, 0x160000);      (* [comment removed for export] *)
    (SA LB_DNB 32, 2 ^ 20 - 32) ]                 (* [comment removed for export] *)
  ++ map sh_zero_of CS_ACC.                        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition MAIN_STK : list (saddr * saddr) :=
  [ (SAsh LB_SB (2 ^ 32) 0, SAsh LB_SB (2 ^ 37) 0);           (* [comment removed for export] *)
    (SAsh LB_ACEIL 0 0, SAsh LB_lit (2 ^ 47) 0);              (* [comment removed for export] *)
    (SAsh LB_lit 0x10000 0, SAsh LB_lit SEGTOP_A 0) ].         (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DEP_RW (h1 : Z) : list (saddr * list scell) :=
  (SA LB_DNB 16, [SC_lit 8 h1]) :: map (fun b => (SA LB_lit (d_tab + 4 * b), [SC_lit 4 (tab_of [h1] b)])) (DEP_BK h1).
Definition SSB_ZERO (f0 : Z) : list (saddr * Z) := [ (SA LB_SSB (8 * f0), 2 ^ 23 - 8 * f0) ].
Definition ushadowZ (n : Z) : list Z := repeat 0 (Z.to_nat (n / 8)) ++ (if Z.eqb (n mod 8) 0 then [] else [n mod 8]).
Definition LIBSH_RO : list (saddr * list scell) := map (fun g => (SAsh LB_lit (gd_beg g) 0, [SC_bytes (ushadowZ (gd_size g))])) GDESC.

Record main_facts (L : layoutA) (h1 : Z) (m : mem) : Prop := mkMF {
  mf_layout : layout_ok L;
  mf_rw : Forall (rw_fact L m) MAIN_RW;
  mf_ro : Forall (ro_fact L m) MAIN_RO;
  mf_zero : Forall (zero_fact L m) MAIN_ZERO;
  mf_stk : Forall (stk_fact L m) MAIN_STK;
  (* [comment removed for export] *)
  mf_stack_sh : bytes_at ctasegs m (shad (l_ACEIL L)) (zrun ((2 ^ 47 - l_ACEIL L) / 8));
  (* [comment removed for export] *)
  mf_h1 : 0 <= h1 < 2 ^ 64;
  mf_dep_rng : Forall (fun b => 0 <= b < 2 ^ 20) (DEP_BK h1);
  mf_dep : Forall (rw_fact L m) (DEP_RW h1);
  mf_ssb : Forall (zero_fact L m) (SSB_ZERO (l_f0 L));
  (* [comment removed for export] *)
  mf_relro : relro_pristine m;
  mf_libsh : Forall (ro_fact L m) LIBSH_RO;
  mf_vis : vis_rep L (l_al0 L ++ allow_main L) m
}.

(* [comment removed for export] *)
Definition sigma_init (L : layoutA) (D : depot) : rtsA :=
  mkRtsA L (fun _ => reg0) (fun _ => []) false [] 0 [] [] [] D (fs0_init 0) (fs0_init 2) (fs0_init 4) (fs0_init 1) (fs0_init 3) false CREDIT0 [] [].
Definition sigma0 (L : layoutA) (h1 : Z) : rtsA := sigma_init L (mkDepot [h1] (l_f0 L)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition no_any (c : scell) : bool := match c with SC_any _ => false | _ => true end.

Lemma den_cells_no_any : forall L cs j1 j2, forallb no_any cs = true -> den_cells L cs j1 = den_cells L cs j2.
Proof.
  intros L cs. induction cs as [|c cs IH]; intros j1 j2 H; [reflexivity|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2].
  cbn [den_cells]. rewrite (IH (tl j1) (tl j2) H2). destruct c; try reflexivity. discriminate H1.
Qed.

(* [comment removed for export] *)
Definition den_tab (L : layoutA) (T : list (saddr * list scell)) : list (Z * list cell) :=
  map (fun e => (den_addr L (fst e), den_cells L (snd e) [])) T.

Ltac in_lit := repeat (first [left; reflexivity | right]).
Ltac in_tab := unfold MAIN_RW, MAIN_RO, MAIN_ZERO, MAIN_STK; repeat (apply in_or_app; first [left; solve [in_lit] | right]); in_lit.

Lemma wr_at_sub : forall (m : mem) a n a' n', wr_at ctasegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at ctasegs m a' n'.
Proof.
  intros m a n a' n' (W0 & W1 & W) H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
Qed.

Lemma wr_at_merge : forall (m : mem) a n1 n2, wr_at ctasegs m a n1 -> wr_at ctasegs m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 -> wr_at ctasegs m a (n1 + n2).
Proof.
  intros m a n1 n2 (A1 & A2 & W1) (B1 & B2 & W2) H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z.ltb_spec0 i n1); [apply W1; lia|]. replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.

Lemma rw_cells_cons : forall (m : mem) a c cs, rw_cells ctasegs m a [c] -> rw_cells ctasegs m (a + Z.of_nat (csize c)) cs ->
  rw_cells ctasegs m a (c :: cs).
Proof.
  intros m a c cs [[Hw1 Hb1] W1] [[Hw2 Hb2] W2]. cbn [cells_wf cells_bytes cells_size] in *. rewrite app_nil_r in Hb1.
  rewrite Nat.add_0_r in W1. split; [split; [split; [exact (proj1 Hw1) | exact Hw2]|]|].
  - apply bytes_at_app. split; [exact Hb1|]. rewrite cbytes_length by exact (proj1 Hw1). exact Hb2.
  - rewrite Nat2Z.inj_add. apply wr_at_merge; [exact W1 | exact W2 | lia | lia].
Qed.

Section Main.
Variables (L : layoutA) (h1 : Z) (m : mem).
Hypothesis MF : main_facts L h1 m.

Lemma mf_rw_get : forall e, In e MAIN_RW -> exists junks, rw_cells ctasegs m (den_addr L (fst e)) (den_cells L (snd e) junks).
Proof. intros e H. exact (proj1 (Forall_forall _ _) (mf_rw L h1 m MF) e H). Qed.
Lemma mf_ro_get : forall e, In e MAIN_RO -> exists junks, ro_cells ctasegs m (den_addr L (fst e)) (den_cells L (snd e) junks).
Proof. intros e H. exact (proj1 (Forall_forall _ _) (mf_ro L h1 m MF) e H). Qed.
Lemma mf_zero_get : forall e, In e MAIN_ZERO -> zero_fact L m e.
Proof. intros e H. exact (proj1 (Forall_forall _ _) (mf_zero L h1 m MF) e H). Qed.
Lemma mf_stk_get : forall e, In e MAIN_STK -> stk_fact L m e.
Proof. intros e H. exact (proj1 (Forall_forall _ _) (mf_stk L h1 m MF) e H). Qed.

(* [comment removed for export] *)
Lemma tab_rw : forall T, incl T MAIN_RW -> forallb (fun e => forallb no_any (snd e)) T = true ->
  forall a cs, In (a, cs) (den_tab L T) -> rw_cells ctasegs m a cs.
Proof.
  intros T HT HN a cs Hin. unfold den_tab in Hin. apply in_map_iff in Hin as (e & E & He). injection E as <- <-.
  destruct (mf_rw_get e (HT e He)) as (junks & X).
  rewrite (den_cells_no_any L (snd e) [] junks (proj1 (forallb_forall _ _) HN e He)). exact X.
Qed.
Lemma tab_ro : forall T, incl T MAIN_RO -> forallb (fun e => forallb no_any (snd e)) T = true ->
  forall a cs, In (a, cs) (den_tab L T) -> ro_cells ctasegs m a cs.
Proof.
  intros T HT HN a cs Hin. unfold den_tab in Hin. apply in_map_iff in Hin as (e & E & He). injection E as <- <-.
  destruct (mf_ro_get e (HT e He)) as (junks & X).
  rewrite (den_cells_no_any L (snd e) [] junks (proj1 (forallb_forall _ _) HN e He)). exact X.
Qed.

Lemma incl_app_l' : forall {X} (a b : list X), incl a (a ++ b). Proof. intros X a b x H. apply in_or_app. left. exact H. Qed.
Lemma incl_app_r' : forall {X} (a b c : list X), incl a c -> incl a (b ++ c). Proof. intros X a b c H x Hx. apply in_or_app. right. exact (H x Hx). Qed.

Lemma LC_consts : forall a cs, In (a, cs) (den_tab L CONSTS_LIT_S) -> rw_cells ctasegs m a cs.
Proof. apply tab_rw; [unfold MAIN_RW; apply incl_app_l'| reflexivity]. Qed.
Lemma LC_tga : forall a cs, In (a, cs) (den_tab L TGA_LIT_S) -> rw_cells ctasegs m a cs.
Proof. apply tab_rw; [unfold MAIN_RW; apply incl_app_r', incl_app_l'| reflexivity]. Qed.
Lemma LC_io : forall a cs, In (a, cs) (den_tab L IO_RW_S) -> rw_cells ctasegs m a cs.
Proof. apply tab_rw; [unfold MAIN_RW; apply incl_app_r', incl_app_r', incl_app_l'| reflexivity]. Qed.
Lemma LC_zero : forall a cs, In (a, cs) (den_tab L ZERO_LIT_S) -> rw_cells ctasegs m a cs.
Proof. apply tab_rw; [unfold MAIN_RW; apply incl_app_r', incl_app_r', incl_app_r', incl_app_r', incl_app_l'| reflexivity]. Qed.
Lemma RC_consts : forall a cs, In (a, cs) (den_tab L CONSTS_RO_S) -> ro_cells ctasegs m a cs.
Proof. apply tab_ro; [unfold MAIN_RO; apply incl_app_l'| reflexivity]. Qed.
Lemma RC_io : forall a cs, In (a, cs) (den_tab L IO_RO_S) -> ro_cells ctasegs m a cs.
Proof. apply tab_ro; [unfold MAIN_RO; apply incl_app_r'; apply incl_refl| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma sym_rw : forall a cs, In (a, cs) MAIN_RW -> forallb no_any cs = true -> rw_cells ctasegs m (den_addr L a) (den_cells L cs []).
Proof. intros a cs H HN. destruct (mf_rw_get (a, cs) H) as (junks & X). cbn [fst snd] in X. rewrite (den_cells_no_any L cs [] junks HN). exact X. Qed.

(* [comment removed for export] *)
Lemma zero_cells : forall a n o cs, In (a, n) MAIN_ZERO \/ zero_fact L m (a, n) -> cells_wf cs -> 0 <= o -> o + Z.of_nat (cells_size cs) <= n ->
  cells_bytes cs = repeat (Z_to_bv 8 0) (cells_size cs) -> rw_cells ctasegs m (den_addr L a + o) cs.
Proof.
  intros a n o cs H Hwf Ho Hle Hz.
  assert (ZF : zero_fact L m (a, n)) by (destruct H as [H|H]; [exact (mf_zero_get _ H)| exact H]).
  destruct ZF as ((B0 & B1 & B) & W). cbn [fst snd] in *. rewrite repeat_length in B1, B.
  assert (Hn : 0 <= n) by lia. rewrite Z2Nat.id in B1 by lia.
  split; [split; [exact Hwf|]|].
  - rewrite Hz. split; [lia|]. split; [rewrite repeat_length; lia|]. intros i Hi. rewrite repeat_length in Hi.
    rewrite nth_error_repeat by lia. replace (den_addr L a + o + Z.of_nat i) with (den_addr L a + Z.of_nat (Z.to_nat o + i)) by lia.
    rewrite (B (Z.to_nat o + i)%nat ltac:(lia)). rewrite nth_error_repeat by lia. reflexivity.
  - apply (wr_at_sub m _ _ _ _ W); lia.
Qed.

Lemma zero_stk : forall a n, In (a, n) MAIN_ZERO \/ zero_fact L m (a, n) -> stk ctasegs m (den_addr L a) (den_addr L a + n).
Proof.
  intros a n H.
  assert (ZF : zero_fact L m (a, n)) by (destruct H as [H|H]; [exact (mf_zero_get _ H)| exact H]).
  destruct ZF as ((B0 & B1 & B) & (W0 & W1 & W)). cbn [fst snd] in *. rewrite repeat_length in B1, B.
  split; [lia|]. split; [lia|]. intros x Hx. split.
  - replace x with (den_addr L a + (x - den_addr L a)) by lia. apply W. lia.
  - exists (Z_to_bv 8 0). replace x with (den_addr L a + Z.of_nat (Z.to_nat (x - den_addr L a))) by lia.
    rewrite (B (Z.to_nat (x - den_addr L a)) ltac:(lia)). apply nth_error_repeat. lia.
Qed.

End Main.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consts.
Variables (L : layoutA) (h1 : Z) (m : mem).
Hypothesis MF : main_facts L h1 m.

Ltac symrw H e := pose proof (sym_rw L h1 m MF (fst e) (snd e) ltac:(in_tab) eq_refl) as H;
  cbn [den_cells den_cell den_addr den_base den_num wcell fst snd hd tl] in H; rewrite ?Z.add_0_l, ?Z.add_0_r in H.

Lemma main_consts : consts_rep L m.
Proof.
  pose proof (LC_consts L h1 m MF) as LC. pose proof (RC_consts L h1 m MF) as RC.
  unfold consts_rep.
  split.
  { unfold inst_cells, RIS_of. split; [|apply LC; in_lit].
    symrw X1 (SA LB_lit i_spacebeg, [SC_ptr (SA LB_SB 0)]). symrw X2 (SA LB_lit i_regioninfo, [SC_ptr (SA LB_SB (2 ^ 37))]).
    apply rw_cells_cons; [exact X1|]. apply rw_cells_cons; [apply LC; in_lit|].
    cbn [csize]. unfold i_spacebeg, i_regioninfo in *. replace (g_instance + 32 + Z.of_nat 8 + Z.of_nat 8) with (g_instance + 48) by lia.
    exact X2. }
  split.
  { unfold mm_gcells. split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; apply LC; in_lit. }
  split.
  { unfold thread_cells, tsd_cells.
    symrw X1 (SA LB_lit g_pthread_tsd_main, [SC_ptr (SA LB_TCX 0)]). symrw X2 (SA LB_TCX 0x98, [SC_ptr (SA LB_T 0)]).
    split; [split; [apply LC; in_lit|]; split; [apply LC; in_lit|]; split; [apply LC; in_lit| exact X1]| exact X2]. }
  split.
  { unfold m2s_cells. split; [apply LC; in_lit|]. split; apply LC; in_lit. }
  split.
  { unfold ps_cells. split; [apply LC; in_lit|]. split; [unfold m2s_cells; split; [apply LC; in_lit|]; split; apply LC; in_lit|].
    split; [unfold setshadow_cells; split; apply LC; in_lit|]. split; apply LC; in_lit. }
  split.
  { unfold stack_cells.
    symrw X1 (SA LB_T off_t_stack_top, [SC_ptr (SA LB_top 0)]). symrw X2 (SA LB_T (off_t_stack_top + 8), [SC_ptr (SA LB_top (-0x800000))]).
    symrw X3 (SA LB_T off_t_stack_switching, [SC_lit 1 0]).
    split; [| exact X3].
    apply rw_cells_cons; [exact X1|]. cbn [csize].
    replace (l_T L + off_t_stack_top + Z.of_nat 8) with (l_T L + (off_t_stack_top + 8)) by lia.
    replace (l_top L - 8388608) with (l_top L + -8388608) by lia. exact X2. }
  split.
  { unfold client_consts. split; [apply RC; in_lit|]. split; [apply RC; in_lit|]. split; [apply RC; in_lit|]. split; [apply RC; in_lit|].
    exact (mf_relro L h1 m MF). }
  unfold icells_rep.
  symrw Y1 (SA LB_T 0xc60, [SC_lit 1 0]). symrw Y2 (SA LB_TCX 8, [SC_lit 4 0]). symrw Y3 (SA LB_T 0, [SC_ptr (SA LB_TCX 0)]).
  split; [exact Y1|].
  repeat (split; [first [apply RC; solve [in_lit] | apply LC; solve [in_lit]]|]).
  split; [exact Y2|].
  split.
  { pose proof (zero_stk L h1 m MF (SA LB_T 2768) 400 ltac:(left; in_tab)) as X. cbn [den_addr den_base] in X.
    replace (l_T L + 3168) with (l_T L + 2768 + 400) by lia. exact X. }
  split; [exact Y3|].
  repeat (split; [first [apply RC; solve [in_lit] | apply LC; solve [in_lit]]|]).
  split; apply Forall_forall; intros [a cs] Hin; [exact (LC_io L h1 m MF a cs Hin) | exact (RC_io L h1 m MF a cs Hin)].
Qed.

End Consts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64s_zero : forall n, u64s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. replace (8 * S n)%nat with (8 + 8 * n)%nat by lia.
  cbn [repeat u64s]. rewrite IH, repeat_app. reflexivity.
Qed.

Section Zero.
Variables (L : layoutA) (h1 : Z) (m : mem).
Hypothesis MF : main_facts L h1 m.
#[local] Notation Σ0 := (sigma0 L h1).

Ltac symrw H e := pose proof (sym_rw L h1 m MF (fst e) (snd e) ltac:(in_tab) eq_refl) as H;
  cbn [den_cells den_cell den_addr den_base den_num wcell fst snd hd tl] in H; rewrite ?Z.add_0_l, ?Z.add_0_r in H.

Lemma main_zero :
  (forall c, 1 <= c <= 31 -> ri_lock m (rinfo (RIS_of (l_SB (lay Σ0))) c) 0
              /\ ri_core m (rinfo (RIS_of (l_SB (lay Σ0))) c) 0 0 0 0
              /\ ri_tail m (rinfo (RIS_of (l_SB (lay Σ0))) c) (Z_to_bv 64 0) (Z_to_bv 8 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] 0 0 0 0 0 0)
  /\ cache_rep Σ0 m /\ sec_rep Σ0 m /\ quar_rep Σ0 m.
Proof.
  pose proof (LC_zero L h1 m MF) as LC.
  pose proof (zero_cells L h1 m MF (SA LB_SB (2 ^ 37 + 128)) (128 * 31)) as Zris. cbn [den_addr den_base] in Zris.
  pose proof (zero_cells L h1 m MF (SA LB_T 0x50) (0xc60 - 0x50)) as Zt. cbn [den_addr den_base] in Zt.
  split.
  { intros c Hc. unfold ri_lock, ri_core, ri_tail, rinfo, RIS_of. cbn [lay sigma0 sigma_init l_SB].
    replace (l_SB L + 2 ^ 37 + 128 * c) with (l_SB L + (2 ^ 37 + 128) + (128 * (c - 1))) by lia.
    split; [apply Zris; [left; in_tab | repeat split | lia | cbn; lia | reflexivity]|].
    split.
    - replace (l_SB L + (2 ^ 37 + 128) + 128 * (c - 1) + 16) with (l_SB L + (2 ^ 37 + 128) + (128 * (c - 1) + 16)) by lia.
      apply Zris; [left; in_tab | repeat split | lia | cbn; lia | reflexivity].
    - replace (l_SB L + (2 ^ 37 + 128) + 128 * (c - 1) + 64) with (l_SB L + (2 ^ 37 + 128) + (128 * (c - 1) + 64)) by lia.
      apply Zris; [left; in_tab | repeat split | lia | cbn; lia | reflexivity]. }
  split.
  { unfold cache_rep. intros c Hc. unfold pclass_rep, pc_cells, pc_addr. cbn [lay sigma0 sigma_init l_T ca ca_init length].
    split.
    - replace (l_T L + 208 + 80 * c) with (l_T L + 0x50 + (128 + 80 * c)) by lia.
      apply Zt; [left; in_tab | repeat split | lia | cbn; lia | reflexivity].
    - exists (repeat (Z_to_bv 64 0) 16). split; [|split; reflexivity].
      assert (X : rw_cells ctasegs m (l_T L + 0x50 + (128 + 80 * c + 16)) [CB 64 (repeat (Z_to_bv 8 0) 64)]).
      { apply Zt; [left; in_tab | cbn; split; [reflexivity | exact I] | lia | cbn; lia | reflexivity]. }
      destruct X as [[_ Xb] Xw]. split.
      + replace (l_T L + 208 + 80 * c + 16) with (l_T L + 0x50 + (128 + 80 * c + 16)) by lia.
        cbn in Xb |- *. exact Xb.
      + replace (l_T L + 208 + 80 * c + 16) with (l_T L + 0x50 + (128 + 80 * c + 16)) by lia. exact Xw. }
  split.
  { unfold sec_rep, sec_core. cbn [lay sigma0 sigma_init l_PAB sec sec_nres length].
    symrw P1 (SA LB_lit i_sec_chunks, [SC_ptr (SA LB_PAB 0)]). symrw P2 (SA LB_lit i_sec_range, [SC_ptr (SA LB_PAB 0)]).
    split.
    - split; [exact P1|]. split; apply LC; in_lit.
    - split; [apply LC; in_lit|]. split.
      + exists []. split; [|split; reflexivity].
        pose proof (mf_layout L h1 m MF) as HL. unfold layout_ok in HL.
        destruct HL as ((_ & SPW) & _ & _ & _ & _ & _ & _ & (G1 & G2 & G3 & _) & _).
        unfold l_ACEIL, STACK_WIN, sp_window_hi in *.
        unfold u64arr. cbn [length Z.of_nat].
        split; [change (u64s []) with (@nil byte); apply bytes_at_nil; lia |].
        split; [lia|]. split; [lia|]. intros i Hi; lia.
      + split; [apply LC; in_lit|].
        split; [unfold sec_range; exact P2|].
        split; [unfold sec_junk; split; [|split] | unfold name_cells; split; apply LC; in_lit].
        * exists (Z_to_bv 8 0), (repeat (Z_to_bv 8 0) 7), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0).
          apply (sec_relist _ _ _ _ (LC i_sec_sorted [CB 40 (repeat (Z_to_bv 8 0) 40)] ltac:(in_lit))); [repeat split | reflexivity].
        * exists (repeat (Z_to_bv 64 0) 64). split; [reflexivity|].
          destruct (LC i_sec_bylog [CB 512 (repeat (Z_to_bv 8 0) 512)] ltac:(in_lit)) as [[_ Hb] Hw]. unfold u64arr.
          rewrite u64s_zero. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. split; [exact Hb|].
          cbn [cells_size csize] in Hw. exact Hw.
        * exists (Z_to_bv 64 0), (Z_to_bv 64 0). apply LC; in_lit. }
  { unfold quar_rep, qcache_rep, qcacheT. cbn [lay sigma0 sigma_init l_T ql qg length map last fold_right qchain].
    split; [split; [| exact I]|].
    - replace (l_T L + 80) with (l_T L + 0x50 + 0) by lia. apply Zt; [left; in_tab | repeat split | lia | cbn; lia | reflexivity].
    - split; [split; [apply LC; in_lit | exact I]|]. apply LC; in_lit. }
Qed.

End Zero.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u8arr_of_seg : forall (m : mem) a n, seg_rw_ok ctasegs a n = true -> 0 <= n -> exists bs, Z.of_nat (length bs) = n /\ u8arr ctasegs m a bs.
Proof.
  intros m a n H Hn. destruct (seg_rw_ok_sound ctasegs a n H m) as [W S].
  destruct (stk_bytes_n ctasegs m a (Z.to_nat n) ltac:(rewrite Z2Nat.id by lia; exact S)) as (bs & Hl & B).
  exists bs. split; [rewrite Hl; apply Z2Nat.id; lia|]. split; [exact B|]. rewrite Hl, Z2Nat.id by lia. exact W.
Qed.

Section FsDepIa.
Variables (L : layoutA) (h1 : Z) (m : mem).
Hypothesis MF : main_facts L h1 m.
#[local] Notation Σ0 := (sigma0 L h1).

Ltac symrw H e := pose proof (sym_rw L h1 m MF (fst e) (snd e) ltac:(in_tab) eq_refl) as H;
  cbn [den_cells den_cell den_addr den_base den_num wcell fst snd hd tl] in H; rewrite ?Z.add_0_l, ?Z.add_0_r in H.

Lemma zero_u8arr : forall a n o k, In (a, n) MAIN_ZERO -> 0 <= o -> o + Z.of_nat k <= n ->
  u8arr ctasegs m (den_addr L a + o) (repeat (Z_to_bv 8 0) k).
Proof.
  intros a n o k H Ho Hk.
  destruct (zero_cells L h1 m MF a n o [CB k (repeat (Z_to_bv 8 0) k)] (or_introl H)
              ltac:(cbn; rewrite repeat_length; split; [reflexivity | exact I]) Ho ltac:(cbn; lia) ltac:(cbn; rewrite app_nil_r, Nat.add_0_r; reflexivity)) as [[_ B] W].
  split; [cbn in B; rewrite app_nil_r in B; exact B|]. cbn in W. rewrite repeat_length. rewrite Nat.add_0_r in W. exact W.
Qed.

Lemma main_ia : ia_rep Σ0 m.
Proof.
  pose proof (LC_zero L h1 m MF) as LC. pose proof (LC_consts L h1 m MF) as LCc.
  unfold ia_rep. exists false. unfold ia_state.
  split; [apply LC; in_lit|]. split; [exists (Z_to_bv 8 0); apply LC; in_lit|].
  split; [exact (u8arr_of_seg m _ _ seg_rw_IAP1 ltac:(lia))|]. split; [exact (u8arr_of_seg m _ _ seg_rw_IAP2 ltac:(lia))|].
  split; [exact (u8arr_of_seg m _ _ seg_rw_IAP3 ltac:(lia))|]. split; [exists (repeat (Z_to_bv 8 0) 40); apply LC; in_lit|].
  split; apply LCc; in_lit.
Qed.

Lemma main_fs : fs_rep Σ0 m.
Proof.
  pose proof (zero_cells L h1 m MF) as ZC.
  pose proof (mf_layout L h1 m MF) as HL. unfold layout_ok in HL.
  destruct HL as ((_ & SPW) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (F1 & F2 & F3 & _) & _).
  unfold l_ACEIL, STACK_WIN, sp_window_hi in F3.
  assert (HF8 : l_FSB L mod 8 = 0).
  { pose proof (Z.div_mod (l_FSB L) 4096 ltac:(lia)) as D. rewrite F2 in D. replace (l_FSB L) with (512 * (l_FSB L / 4096) * 8) by lia. apply Z.mod_mul. lia. }
  unfold fs_rep. cbn [lay sigma0 sigma_init l_FSB l_DTV l_T fs0 fs2 fs4 fs1 fs3].
  assert (CLS : forall c, c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 -> fs_cls_rep (l_FSB L) c (fs0_init c) m).
  { intros c Hc. unfold fs_cls_rep, fs0_init. cbn [fss_hint fss_flags].
    assert (HNF : 0 < NF c <= 2 ^ 14) by (destruct Hc as [Hc | [Hc | [Hc | [Hc | Hc]]]]; subst c; unfold NF; cbn; lia).
    split; [|split].
    - unfold fs_hint. replace (l_FSB L + 8 * c) with (den_addr L (SA LB_FSB 0) + 8 * c) by (cbn [den_addr den_base]; lia).
      apply (ZC (SA LB_FSB 0) 0x58); [left; in_tab | repeat split | lia | cbn; destruct Hc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; lia | reflexivity].
    - unfold fs_flags, fl_base. rewrite map_repeat. change (b8 0) with (Z_to_bv 8 0).
      replace (l_FSB L + 0x1000 + flags_off c) with (den_addr L (SA LB_FSB 0x1000) + flags_off c) by (cbn [den_addr den_base]; lia).
      apply (zero_u8arr (SA LB_FSB 0x1000) 0xb08000); [in_tab | destruct Hc as [Hc | [Hc | [Hc | [Hc | Hc]]]]; subst c; cbv [flags_off]; lia
                                        | rewrite Z2Nat.id by lia; destruct Hc as [Hc | [Hc | [Hc | [Hc | Hc]]]]; subst c; cbv [flags_off NF]; lia].
    - unfold fs_free_frames. intros p Hp _. split.
      + exists (repeat (Z_to_bv 8 0) (Z.to_nat (fsz c))). unfold frame_addr.
        replace (l_FSB L + 0x9000 + c * 2 ^ 20 + p * fsz c) with (den_addr L (SA LB_FSB 0x1000) + (0x8000 + c * 2 ^ 20 + p * fsz c)) by (cbn [den_addr den_base]; lia).
        assert (Hfr : 0 <= 0x8000 + c * 2 ^ 20 + p * fsz c /\ 0x8000 + c * 2 ^ 20 + p * fsz c + fsz c <= 0xb08000 /\ 0 < fsz c).
        { destruct Hc as [Hc | [Hc | [Hc | [Hc | Hc]]]]; subst c; cbv [fsz NF] in *; lia. }
        apply (ZC (SA LB_FSB 0x1000) 0xb08000); [left; in_tab | cbn; rewrite repeat_length; split; [reflexivity | exact I] | lia
                                 | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia
                                 | cbn; rewrite app_nil_r, Nat.add_0_r; reflexivity].
      + exists (repeat (Z_to_bv 8 0) (Z.to_nat (fsz c / 8))). unfold frame_addr.
        assert (Hfr : 0 <= c * 2 ^ 20 + p * fsz c /\ (c * 2 ^ 20 + p * fsz c) / 8 + fsz c / 8 <= 0x160000 /\ 0 < fsz c /\ fsz c mod 8 = 0).
        { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          destruct Hc as [Hc | [Hc | [Hc | [Hc | Hc]]]]; subst c; cbv [fsz NF] in *; lia.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
        assert (E8 : shad (l_FSB L + 0x9000 + c * 2 ^ 20 + p * fsz c)
                     = den_addr L (SAsh LB_FSB 0 0x1200) + ((c * 2 ^ 20 + p * fsz c) / 8)).
        { cbn [den_addr den_base]. unfold shad.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
        rewrite E8.
        apply (ZC (SAsh LB_FSB 0 0x1200) 0x160000); [left; in_tab | cbn; rewrite repeat_length; split; [reflexivity | exact I] | apply Z.div_pos; lia
                                 | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia); lia
                                 | cbn; rewrite app_nil_r, Nat.add_0_r; reflexivity]. }
  symrw C0 (SA LB_FSB 0x58, [SC_lit 8 20; SC_lit 1 0]). symrw C1' (SA LB_lit tpA, [SC_ptr (SA LB_FSB 0)]).
  symrw C2' (SA LB_lit g_tls_dtls, [SC_ptr (SA LB_DTV 0)]). symrw C3 (SA LB_DTV 24, [SC_lit 8 0xba93f0]). symrw C4' (SA LB_T 48, [SC_lit 8 0xba9b28; SC_lit 8 0xba9c14]).
  split; [exact C0|].
  split; [apply CLS; lia|]. split; [apply CLS; lia|]. split; [split; [|split]; apply CLS; lia|].
  split; [exact C1'|].
  split.
  - exists 0xba93f0. split; [lia|].
    pose proof (LC_tga L h1 m MF) as LC.
    unfold tga_cells, dtls_cells. split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|].
    split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|].
    split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|].
    split; [exact C2'| exact C3].
  - split; [|unfold fs_busy; cbn [frames sigma0 sigma_init]; constructor].
    exists (Z_to_bv 64 0xba9b28), (Z_to_bv 64 0xba9c14). unfold ttls_cells. exact C4'.
Qed.

Lemma main_dep : dep_rep (lay Σ0) (dep Σ0) m.
Proof.
  pose proof (mf_dep L h1 m MF) as DR. unfold DEP_RW in DR. apply Forall_cons_iff in DR as [DN DT].
  destruct DN as (jn & DN). cbn [den_cells den_cell den_addr den_base wcell fst snd hd tl] in DN.
  unfold dep_rep, depot_rep, d_n, sigma0, sigma_init. cbn [lay dep l_DNB l_SSB d_hs d_tot length].
  change (hash_of [h1] 1) with h1.
  symrw D1 (SA LB_lit d_nuniq, [SC_lit 4 1]). symrw D2 (SA LB_lit d_map1, [SC_ptr (SA LB_DNB 0)]). symrw D3 (SA LB_DNB 24, [SC_lit 4 0; SC_lit 4 1]).
  symrw D4 (SA LB_lit s_total, [SC_num 8 LN_f0]). symrw D5 (SA LB_lit s_data0, [SC_ptr (SA LB_SSB 0)]). symrw D6 (SA LB_lit s_stored0, [SC_num 4 LN_f0]).
  split.
  { intros b Hb. split; [exact (proj1 (Forall_forall _ _) (mf_dep_rng L h1 m MF) b Hb)|].
    pose proof (proj1 (Forall_forall _ _) DT (SA LB_lit (d_tab + 4 * b), [SC_lit 4 (tab_of [h1] b)]) ltac:(apply in_map_iff; exists b; split; [reflexivity| exact Hb])) as (jb & X).
    cbn [den_cells den_cell den_addr den_base wcell fst snd hd tl] in X. rewrite Z.add_0_l in X. exact X. }
  split; [exact D1|].
  split; [exact D2|].
  split.
  { intros i Hi. assert (i = 1) by lia. subst i. exists (Z_to_bv 64 1).
    apply rw_cells_cons; [replace (l_DNB L + 16 * 1) with (l_DNB L + 16) by lia; exact DN|].
    cbn [csize]. replace (l_DNB L + 16 * 1 + Z.of_nat 8) with (l_DNB L + 24) by lia. exact D3. }
  split.
  { replace (l_DNB L + 16 * (Z.of_nat 1 + 1)) with (den_addr L (SA LB_DNB 32)) by (cbn [den_addr den_base]; lia).
    replace (l_DNB L + 2 ^ 20) with (den_addr L (SA LB_DNB 32) + (2 ^ 20 - 32)) by (cbn [den_addr den_base]; lia).
    apply (zero_stk L h1 m MF). left. in_tab. }
  split; [exact D4|].
  split; [exact D5|].
  split; [exact D6|].
  pose proof (mf_ssb L h1 m MF) as ZS. unfold SSB_ZERO in ZS. apply Forall_cons_iff in ZS as [ZS _].
  replace (l_SSB L + 8 * l_f0 L) with (den_addr L (SA LB_SSB (8 * l_f0 L))) by reflexivity.
  replace (l_SSB L + 2 ^ 23) with (den_addr L (SA LB_SSB (8 * l_f0 L)) + (2 ^ 23 - 8 * l_f0 L)) by (cbn [den_addr den_base]; lia).
  apply (zero_stk L h1 m MF). right. exact ZS.
Qed.

End FsDepIa.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ushadowZ_den : forall n, map (Z_to_bv 8) (ushadowZ n) = ushadow n.
Proof.
  intros n. unfold ushadowZ, ushadow. rewrite map_app, map_repeat. f_equal. destruct (n mod 8 =? 0); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma acc_of_zero_shadow : forall (m : mem) lo hi, 0 <= lo -> lo < hi ->
  bytes_at ctasegs m (shad lo) (repeat (Z_to_bv 8 0) (Z.to_nat ((hi - 1) / 8 - lo / 8 + 1))) -> acc ctasegs m lo (hi - lo).
Proof.
  intros m lo hi H0 Hlh (B0 & B1 & B) i Hi. rewrite repeat_length in B1, B.
  assert (Hq : 0 <= (lo + i) / 8 - lo / 8 < (hi - 1) / 8 - lo / 8 + 1).
  { split; [assert (lo / 8 <= (lo + i) / 8) by (apply Z.div_le_mono; lia); lia
           | assert ((lo + i) / 8 <= (hi - 1) / 8) by (apply Z.div_le_mono; lia); lia]. }
  exists (Z_to_bv 8 0). split; [| left; reflexivity].
  split; [unfold shad in *; lia|]. split; [cbn [length]; unfold shad in *; lia|].
  intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. rewrite Z.add_0_r. cbn [nth_error].
  replace (shad (lo + i)) with (shad lo + Z.of_nat (Z.to_nat ((lo + i) / 8 - lo / 8))) by (unfold shad; lia).
  rewrite (B (Z.to_nat ((lo + i) / 8 - lo / 8)) ltac:(lia)). apply nth_error_repeat. lia.
Qed.

Section Shadow.
Variables (L : layoutA) (h1 : Z) (m : mem).
Hypothesis MF : main_facts L h1 m.
#[local] Notation Σ0 := (sigma0 L h1).

Lemma main_lib_sh : lib_sh m.
Proof.
  unfold lib_sh. apply Forall_forall. intros g Hg.
  pose proof (proj1 (Forall_forall _ _) (mf_libsh L h1 m MF) (SAsh LB_lit (gd_beg g) 0, [SC_bytes (ushadowZ (gd_size g))])
                ltac:(unfold LIBSH_RO; apply in_map_iff; exists g; split; [reflexivity| exact Hg])) as (junks & [_ X]).
  cbn [den_cells den_cell den_addr den_base fst snd cells_bytes cbytes] in X. rewrite app_nil_r, ushadowZ_den, Z.add_0_l, Z.add_0_r in X. exact X.
Qed.

Lemma main_static_acc : static_acc m.
Proof.
  unfold static_acc. apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
  assert (Hr : 0x10000 <= lo /\ lo < hi /\ hi <= 0xbcacd0).
  { unfold CS_ACC in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. }
  assert (HZ : In (sh_zero_of (lo, hi)) MAIN_ZERO).
  { unfold MAIN_ZERO. apply in_or_app. right. apply in_map. exact Hin. }
  destruct (mf_zero_get L h1 m MF _ HZ) as [X _]. unfold sh_zero_of in X. cbn [fst snd den_addr den_base] in X.
  rewrite Z.add_0_l, Z.add_0_r in X. apply acc_of_zero_shadow; [lia | lia | exact X].
Qed.

Lemma main_shadow : shadow_rep (lay Σ0) m.
Proof.
  unfold shadow_rep. cbn [lay sigma0 sigma_init].
  split; [exact (mf_stack_sh L h1 m MF)|].
  split.
  { pose proof (mf_stk_get L h1 m MF (SAsh LB_ACEIL 0 0, SAsh LB_lit (2 ^ 47) 0) ltac:(in_tab)) as X. unfold stk_fact in X.
    cbn [fst snd den_addr den_base] in X. rewrite ?Z.add_0_l, ?Z.add_0_r in X. exact X. }
  split.
  { pose proof (mf_stk_get L h1 m MF (SAsh LB_lit 0x10000 0, SAsh LB_lit SEGTOP_A 0) ltac:(in_tab)) as X. unfold stk_fact in X.
    cbn [fst snd den_addr den_base] in X. rewrite ?Z.add_0_l, ?Z.add_0_r in X.
    change (pg_dn (shad 0x10000)) with (shad 0x10000). exact X. }
  split; [exact main_static_acc | exact main_lib_sh].
Qed.

Lemma main_prim : prim_rep Σ0 m.
Proof.
  pose proof (main_zero L h1 m MF) as (RI & _).
  pose proof (mf_layout L h1 m MF) as HL. unfold layout_ok in HL.
  destruct HL as ((SPL & SPW) & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & Hsb & _).
  unfold l_ACEIL, STACK_WIN, sp_window_hi, sp_window_lo in *.
  pose proof (mf_stk_get L h1 m MF (SAsh LB_SB (2 ^ 32) 0, SAsh LB_SB (2 ^ 37) 0) ltac:(in_tab)) as SH. unfold stk_fact in SH.
  cbn [fst snd den_addr den_base] in SH. rewrite ?Z.add_0_r in SH.
  unfold prim_rep. intros c Hc. cbn [pr sigma0 sigma_init]. unfold reg_rep, reg0. cbn [r_st r_fl r_mfa r_muser length]. cbn [lay sigma0 sigma_init l_SB].
  destruct (RI c Hc) as (R1 & R2 & R3). cbn [lay sigma0 sigma_init l_SB] in R1, R2, R3.
  rewrite Z.mul_0_r. split; [exact R1|]. split; [exact R2|]. split; [eexists _, _, _, _, _, _, _, _, _; exact R3|].
  assert (HSB : 0 <= l_SB L < 2 ^ 47) by lia.
  unfold rb, fa. split.
  { exists []. split; [|split; reflexivity]. unfold fl_arr, u32arr, fa, rb. change (u32s []) with (@nil byte). cbn [length Z.of_nat].
    split; [apply bytes_at_nil; lia|]. split; [lia|]. split; [lia|]. intros i Hi; lia. }
  split; [split; [lia|]; split; [lia|]; intros a Ha; lia|].
  split.
  { change (farun ((0 - 0) / 8)) with (@nil byte). apply bytes_at_nil. unfold shad, SHB.
    assert (0 <= (l_SB L + c * 2 ^ 32 + 0) / 8 <= 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
  assert (Hin : shad (l_SB L + 2 ^ 32) <= shad (l_SB L + c * 2 ^ 32)
                /\ shad (l_SB L + c * 2 ^ 32 + 2 ^ 32) <= shad (l_SB L + 2 ^ 37)).
  { unfold shad. split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia. }
  destruct SH as (S0 & S1 & S2). split; [lia|]. split; [lia|]. intros a Ha. apply S2. lia.
Qed.

End Shadow.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma nbusy_repeat0 : forall n, nbusy (repeat 0 n) = 0%nat.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat nbusy]. rewrite IH. reflexivity. Qed.

Lemma fs_cls_wf_init : forall c, 0 <= c <= 14 -> fs_cls_wf c (fs0_init c).
Proof.
  intros c Hc. unfold fs_cls_wf, fs0_init, flags_ok. cbn [fss_flags fss_hint].
  rewrite repeat_length, nbusy_repeat0. split; [split|].
  - rewrite Z2Nat.id; [reflexivity|]. unfold NF. apply Z.pow_nonneg. lia.
  - apply Forall_forall. intros z Hz. apply repeat_spec in Hz. left. exact Hz.
  - split; [lia| cbn; lia].
Qed.

Lemma ClassSize_nonneg : forall c, 1 <= c -> 0 <= ClassSize c.
Proof.
  intros c Hc. unfold ClassSize. destruct (c =? 31); [lia|]. destruct (c <=? 16); [lia|].
  assert (T : 0 <= Z.shiftl 512 ((c - 16) / 2)) by (apply Z.shiftl_nonneg; lia).
  assert (0 <= c mod 2) by (apply Z.mod_pos_bound; lia). assert (0 <= Z.shiftl 512 ((c - 16) / 2) / 2) by (apply Z.div_pos; lia).
  nia.
Qed.

Lemma ClassSize_pos0 : forall c, 1 <= c <= 31 -> 0 < ClassSize c.
Proof.
  intros c Hc. unfold ClassSize. destruct (c =? 31); [lia|]. destruct (c <=? 16) eqn:H16; [lia|].
  assert (T : 512 <= Z.shiftl 512 ((c - 16) / 2)).
  { rewrite Z.shiftl_mul_pow2 by (apply Z.div_pos; lia). pose proof (Z.pow_pos_nonneg 2 ((c - 16) / 2) ltac:(lia) ltac:(apply Z.div_pos; lia)). nia. }
  assert (0 <= c mod 2) by (apply Z.mod_pos_bound; lia). assert (0 <= Z.shiftl 512 ((c - 16) / 2) / 2) by (apply Z.div_pos; lia). nia.
Qed.

Lemma reg_wf_0 : forall c, 1 <= c <= 31 -> reg_wf c reg0.
Proof.
  intros c Hc. pose proof (ClassSize_pos0 c Hc) as Hcs. unfold reg_wf, reg0, kUserCap, kUMap, kFaCap.
  cbn [r_muser r_mfa r_st r_fl length]. repeat split; try lia; constructor.
Qed.

Lemma sum_cls_0 : forall k, sum_cls (fun _ => 0 + 0) k = 0.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [sum_cls]. rewrite IH. reflexivity. Qed.

Lemma rt_wf_init : forall L D, layout_ok L -> depot_ok D (l_DNB L) (l_SSB L) (l_ACEIL L) ->
  d_n D + 2 < 2 ^ 16 -> d_tot D + 255 < 2 ^ 20 -> dep_inv D -> rt_wf (sigma_init L D).
Proof.
  intros L D HL HD H1 H2 H3. unfold rt_wf. split; [exact HL|]. split.
  { unfold regs_wf. cbn [pr ca ca_init sigma_init]. split; [exact reg_wf_0|]. split; [intros; reflexivity|].
    split; [|split; [intros _ c; reflexivity | split; [intros c i Hc Hi; cbn [r_st reg0] in Hi; destruct i; discriminate Hi | intros _ c; reflexivity]]].
    intros c Hc. cbn [length app]. split; [unfold MaxCount; lia|]. split; constructor. }
  split.
  { unfold live_wf. cbn [live pr sec sigma_init]. split; [exact live_caps_nil|]. split; [constructor|].
    split; [intros p n []|]. split; [intros c i n _ Hn; destruct i; discriminate|]. intros s []. }
  split.
  { unfold sec_wf. cbn [sec sec_nres sigma_init length]. split; [unfold SEC_MAX; lia|]. split; [left; reflexivity|].
    split; [intros H; exfalso; apply H; reflexivity|]. split; [constructor|].
    split; [intros k1 k2 s1 s2 Hk; destruct k1; discriminate| constructor]. }
  split.
  { unfold quar_wf, qbytes, qsum. cbn [ql qg sigma_init fold_right length app map]. unfold QMAX_L, QMAX_G.
    split; [lia|]. split; [lia|]. split; [constructor|]. split; [constructor|]. split; [constructor|].
    unfold qents. cbn [ql qg sigma_init app flat_map map]. split; [constructor|]. split; [constructor|].
    intros c i Hc Hi. cbn [pr sigma_init r_st reg0] in Hi. destruct i; discriminate Hi. }
  split.
  { unfold fs_wf. cbn [fs0 fs2 fs4 fs1 fs3 frames sigma_init]. split; [apply fs_cls_wf_init; lia|]. split; [apply fs_cls_wf_init; lia|].
    split; [split; [|split]; apply fs_cls_wf_init; lia|]. split; [constructor|]. split; [constructor|]. split; [cbn; lia|].
    split; intros k Hk; destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; unfold sigma_init;
      cbn [fs_of fs0 fs2 fs4 fs1 fs3 fss_flags fss_hint fs0_init frames List.filter length credit];
      first [rewrite nbusy_repeat0; reflexivity | lia]. }
  split.
  { unfold budget_wf. cbn [credit aw sigma_init]. unfold CREDIT0. split; [lia|]. split; [constructor|]. split; [cbn; lia|].
    split; [unfold rt_eager; cbn [pr sec sec_nres sigma_init r_muser r_mfa reg0 fold_right]; rewrite sum_cls_0; lia|].
    unfold secsum. cbn [sec sigma_init fold_right]. lia. }
  split; [exact HD|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [intros c i n Hc Hi; cbn [pr sigma_init r_st reg0] in Hi; destruct i; discriminate Hi | intros s Hs; destruct Hs].
Qed.


Section Art.
Variables (L : layoutA) (h1 : Z) (m : mem).
Hypothesis MF : main_facts L h1 m.
#[local] Notation Σ0 := (sigma0 L h1).

Lemma main_depot_ok : depot_ok (mkDepot [h1] (l_f0 L)) (l_DNB L) (l_SSB L) (l_ACEIL L).
Proof.
  pose proof (mf_layout L h1 m MF) as HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GD & GS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf0 & _ & _ & _ & HDS & _).
  unfold grant_ok in GD, GS. unfold depot_ok, d_n. cbn [d_hs d_tot length].
  split; [constructor; [exact (mf_h1 L h1 m MF)| constructor]|]. split; [lia|]. split; [lia|].
  unfold apart in HDS. unfold SEGTOP_A in *. lia.
Qed.

Lemma main_rt_wf : rt_wf Σ0.
Proof.
  pose proof (mf_layout L h1 m MF) as HL. pose proof HL as HL'. unfold layout_ok in HL'.
  destruct HL' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf0 & _).
  apply rt_wf_init; [exact HL | exact main_depot_ok | unfold d_n; cbn; lia | cbn [d_tot]; lia |].
  unfold dep_inv, d_n. cbn [d_hs d_tot length]. split; [constructor; [intros []| constructor]|].
  split; [intros h [<-|[]]; left; reflexivity|]. split; [lia | unfold DEP_WMAX; cbn; lia].   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Theorem main_art : ART_A Σ0 m.
Proof.
  pose proof (main_zero L h1 m MF) as (_ & Zc & Zs & Zq).
  apply ART_intro.
  - exact main_rt_wf.
  - exact (main_consts L h1 m MF).
  - exact (main_prim L h1 m MF).
  - exact Zc.
  - unfold chunk_rep. cbn [pr sec sigma0 sigma_init r_st reg0]. split; [intros c i st _ Hn; destruct i; discriminate | intros k s' Hk; destruct k; discriminate].
  - exact Zs.
  - exact Zq.
  - exact (main_dep L h1 m MF).
  - exact (main_fs L h1 m MF).
  - exact (main_ia L h1 m MF).
  - exact (main_shadow L h1 m MF).
  - exact (mf_vis L h1 m MF).
Qed.

End Art.

(* [comment removed for export] *)
Lemma sigma0_lay : forall L h1, lay (sigma0 L h1) = L. Proof. reflexivity. Qed.
Lemma sigma0_aw : forall L h1, aw (sigma0 L h1) = []. Proof. reflexivity. Qed.
Lemma sigma0_maps : forall L h1, rt_maps (sigma0 L h1) = l_maps0 L. Proof. reflexivity. Qed.
Lemma sigma0_allow : forall L h1, rtA_allow (sigma0 L h1) = l_al0 L ++ allow_main L. Proof. reflexivity. Qed.
Lemma sigma0_live : forall L h1, live (sigma0 L h1) = [] /\ frames (sigma0 L h1) = [] /\ credit (sigma0 L h1) = CREDIT0. Proof. intros. repeat split. Qed.
