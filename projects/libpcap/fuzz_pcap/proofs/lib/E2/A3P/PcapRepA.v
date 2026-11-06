(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import GIA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ceil_facts := idtac.

Record pcap_consts := mkPK {
  pk_next_pcap : Z;     (* [comment removed for export] *)
  pk_next_ng : Z;       (* [comment removed for export] *)
  pk_cleanup_sf : Z;    (* [comment removed for export] *)
  pk_cleanup_ng : Z;    (* [comment removed for export] *)
  pk_oneshot : Z;       (* [comment removed for export] *)
  pk_stats : Z          (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition PK : pcap_consts := mkPK 0x88188 0x8cb68 0x84c40 0x8dc50 0x858e4 0x85828.

Definition PCAP_NEXT_EX_ENTRY : Z := 0x8597c.
Definition PCAP_OFFLINE_READ_ENTRY : Z := 0x85404.
Definition PCAP_STATS_ENTRY : Z := 0x85ef4.
Definition PCAP_CLOSE_ENTRY : Z := 0x85c2c.
Definition PCAP_FREECODE_ENTRY : Z := 0x85854.
Definition PCAP_OPEN_OFFLINE_ENTRY : Z := 0x853e0.
Definition PCAP_OPEN_OFFLINE_WTP_ENTRY : Z := 0x84ce8.
Definition PCAP_FOPEN_OFFLINE_WTP_ENTRY : Z := 0x84e8c.
Definition PCAP_OPEN_OFFLINE_COMMON_ENTRY : Z := 0x85ccc.
Definition PCAP_CHECK_HEADER_ENTRY : Z := 0x8763c.
Definition PCAP_NG_CHECK_HEADER_ENTRY : Z := 0x8ace8.
Definition PCAP_ADJUST_SNAPSHOT_ENTRY : Z := 0x853ec.
Definition LINKTYPE_TO_DLT_ENTRY : Z := 0x88e50.
Definition MAX_SNAPLEN_ENTRY : Z := 0x88ec8.
Definition PCAP_POST_PROCESS_ENTRY : Z := 0x88f00.
Definition PCAP_STRERROR_ENTRY : Z := 0x85e48.
Definition PCAP_FMT_ERRMSG_ENTRY : Z := 0x85f80.
Definition READ_BYTES_ENTRY : Z := 0x8ba38.
Definition READ_BLOCK_ENTRY : Z := 0x8bb44.
Definition ADD_INTERFACE_ENTRY : Z := 0x8c1c8.
Definition FILE_BLOCK : Z := 1264.    (* [comment removed for export] *)
Definition PCAP_HDR_OFF : Z := 520.   (* [comment removed for export] *)
Definition PCAP_ERRBUF_OFF : Z := 216.
Definition PCAP_PRIV_OFF : Z := 648.  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma eqz_false : forall z, (0 < z < 2^64)%Z -> bv_eqb (Z_to_bv 64 z) z64 = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.
Lemma nez_true : forall z, (0 < z < 2^64)%Z -> negb (bv_eqb (Z_to_bv 64 z) z64) = true.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. Qed.
Lemma eqb_lits_false : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y Hx Hy Hne. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact Hne. Qed.

(* [comment removed for export] *)
Lemma and7_aligned : forall x, (0 <= x < 2^64)%Z -> (x mod 8 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0%Z.
Proof.
  intros x Hx Ha. rewrite unsigned_lit by lia. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Ha.
Qed.
Lemma and3_aligned : forall x, (0 <= x < 2^64)%Z -> (x mod 4 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 x)) 3 = 0%Z.
Proof.
  intros x Hx Ha. rewrite unsigned_lit by lia. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2)%Z with 4%Z. exact Ha.
Qed.
Lemma aligned16_8 : forall x k, (x mod 16 = 0)%Z -> (k mod 8 = 0)%Z -> ((x + k) mod 8 = 0)%Z.
Proof.
  intros x k Hx Hk. rewrite Z.add_mod, Hk, Z.add_0_r by lia. rewrite Z.mod_mod by lia.
  apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->]. replace (q * 16)%Z with ((q * 2) * 8)%Z by lia. apply Z.mod_mul.
  all: lia.
Qed.
Section Rep.
  Context {CEILV : Ceiling.CEIL} {H hptr : Type} (HO : HeapOps H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).

  Definition b8 (z : Z) : byte := Z_to_bv 8 z.

  Definition is_ng (p : pcapT) : bool := match pc_priv p with PrivNg _ _ => true | PrivPcap _ => false end.
  Definition np_entry (p : pcapT) : Z := if is_ng p then pk_next_ng PK else pk_next_pcap PK.
  Definition cleanup_entry (p : pcapT) : Z := if is_ng p then pk_cleanup_ng PK else pk_cleanup_sf PK.
  (* [comment removed for export] *)
  Definition psize (p : pcapT) : Z := if is_ng p then PCAP_NG_SF_TOTAL else PCAP_SF_TOTAL.

  (* [comment removed for export] *)
  Definition hdr_cells (h : pkthdr) : list cell :=
    [C8 (Z_to_bv 64 (h_sec h)); C8 (Z_to_bv 64 (h_usec h)); C4 (Z_to_bv 64 (h_caplen h)); C4 (Z_to_bv 64 (h_len h))].

  (* [comment removed for export] *)
  Record pcap_junk := mkPJ {
    pj_read_op : word;      (* [comment removed for export] *)
    pj_fd : word;           (* [comment removed for export] *)
    pj_a : list byte;       (* [comment removed for export] *)
    pj_b : list byte;       (* [comment removed for export] *)
    pj_c : list byte;       (* [comment removed for export] *)
    pj_d : list byte;       (* [comment removed for export] *)
    pj_e : list byte;       (* [comment removed for export] *)
    pj_f : list byte;       (* [comment removed for export] *)
    pj_g : list byte;       (* [comment removed for export] *)
    pj_h : list byte;       (* [comment removed for export] *)
    pj_breakloop : word     (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pc_pre (p : pcapT) (P B : Z) (rf : cell) (j : pcap_junk) : list cell :=
    [ C8 (pj_read_op j);                         (* [comment removed for export] *)
      C8 (Z_to_bv 64 (np_entry p));              (* [comment removed for export] *)
      C4 (pj_fd j);                              (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_bufsize p));            (* [comment removed for export] *)
      C8 (Z_to_bv 64 B);                         (* [comment removed for export] *)
      CB 12 (pj_a j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_break_loop p));         (* [comment removed for export] *)
      C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF));       (* [comment removed for export] *)
      C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)));    (* [comment removed for export] *)
      CB 4 (pj_b j);                             (* [comment removed for export] *)
      rf;                                        (* [comment removed for export] *)
      CB 16 (pj_c j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_version_major p));      (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_version_minor p));      (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_snapshot p));           (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_linktype p));           (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_linktype_ext p));       (* [comment removed for export] *)
      CB 12 (pj_d j);                            (* [comment removed for export] *)
      C8 (Z_to_bv 64 0);                         (* [comment removed for export] *)
      CB 28 (pj_e j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_tstamp_precision p));   (* [comment removed for export] *)
      CB 48 (pj_f j);                            (* [comment removed for export] *)
      C8 (Z_to_bv 64 0) ].                       (* [comment removed for export] *)
  Definition pc_ops (p : pcapT) (st os : cell) (j : pcap_junk) : list cell :=
    [ CB 72 (pj_h j);                            (* [comment removed for export] *)
      st;                                        (* [comment removed for export] *)
      C8 (pj_breakloop j);                       (* [comment removed for export] *)
      os;                                        (* [comment removed for export] *)
      C8 (Z_to_bv 64 (cleanup_entry p)) ].       (* [comment removed for export] *)
  Definition pcap_cells_gen (p : pcapT) (P B : Z) (rf st os : cell) (j : pcap_junk) : list cell :=
    pc_pre p P B rf j ++ [CB 304 (pj_g j)] (* [comment removed for export] *) ++ hdr_cells (pc_header p) (* [comment removed for export] *) ++ pc_ops p st os j.

  Definition pcap_cells (p : pcapT) (P B Af : Z) (j : pcap_junk) : list cell :=
    pcap_cells_gen p P B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j.

  #[using="Type"] Remark pcap_cells_size : forall p P B Af j, cells_size (pcap_cells p P B Af j) = 648%nat.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition lenswap_code (l : lenswap_t) : Z := match l with NOT_SWAPPED => 0 | SWAPPED => 1 | MAYBE_SWAPPED => 2 end.
  Definition sfscale_code (t : sf_scale_t) : Z := match t with SF_PASS_THROUGH => 0 | SF_SCALE_UP => 1 | SF_SCALE_DOWN => 2 end.
  Definition ngscale_code (t : ng_scale_t) : Z :=
    match t with NG_PASS_THROUGH => 0 | SCALE_UP_DEC => 1 | SCALE_DOWN_DEC => 2 | SCALE_UP_BIN => 3 | SCALE_DOWN_BIN => 4 end.
  Definition is_dec (t : ng_scale_t) : bool := match t with SCALE_UP_DEC | SCALE_DOWN_DEC => true | _ => false end.

  (* [comment removed for export] *)
  Definition sf_cells (s : pcap_sf) : list cell :=
    [C8 (Z_to_bv 64 (sf_hdrsize s)); C4 (Z_to_bv 64 (lenswap_code (sf_lengths_swapped s))); C4 (Z_to_bv 64 (sfscale_code (sf_scale_type s)))].
  (* [comment removed for export] *)
  Definition ng_cells (s : pcap_ng_sf) (I : Z) (pad : list byte) : list cell :=
    [C8 (Z_to_bv 64 (ng_user_tsresol s)); C4 (Z_to_bv 64 (ng_max_blocksize s)); C4 (Z_to_bv 64 (ng_ifcount s));
     C4 (Z_to_bv 64 (ng_ifaces_size s)); CB 4 pad; C8 (Z_to_bv 64 I)].
  Definition priv_cells (p : pcapT) (I : Z) (pad : list byte) : list cell :=
    match pc_priv p with PrivPcap s => sf_cells s | PrivNg s _ => ng_cells s I pad end.

  (* [comment removed for export] *)
  Record if_junk := mkIJ { ij_p1 : list byte; ij_p2 : list byte; ij_sf : word }.
  Definition if_cells (i : ng_if) (j : if_junk) : list cell :=
    [C4 (Z_to_bv 64 (if_snaplen i)); CB 4 (ij_p1 j); C8 (Z_to_bv 64 (if_tsresol i)); C4 (Z_to_bv 64 (ngscale_code (if_scale_type i)));
     CB 4 (ij_p2 j); C8 (if is_dec (if_scale_type i) then Z_to_bv 64 (if_scale_factor i) else ij_sf j); C8 (Z_to_bv 64 (if_tsoffset i))].
  Fixpoint ifs_cells (ifs : list ng_if) (js : list if_junk) : list cell :=
    match ifs, js with
    | i :: ifs', j :: js' => if_cells i j ++ ifs_cells ifs' js'
    | _, _ => []
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition if_wf (i : ng_if) : Prop :=
    0 < if_tsresol i < 2^64 /\ (is_dec (if_scale_type i) = true -> 0 < if_scale_factor i < 2^64).

  Definition ifaces_ok (p : pcapT) (I : Z) (m : mem) : Prop :=
    match pc_priv p with
    | PrivPcap _ => I = 0
    | PrivNg s None => I = 0 /\ ng_ifaces s = [] /\ ng_ifcount s = 0 /\ ng_ifaces_size s = 0
    | PrivNg s (Some q) =>
        exists js tail, length js = length (ng_ifaces s)
          /\ rw_cells asegs m I (ifs_cells (rev (ng_ifaces s)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) tail])
          /\ ng_ifcount s = Z.of_nat (length (ng_ifaces s)) /\ ng_ifcount s <= ng_ifaces_size s /\ 1 <= ng_ifaces_size s < 2^26
          /\ Forall if_wf (ng_ifaces s)
    end.

  (* [comment removed for export] *)
  Definition pcap_blocks (p : pcapT) (P B I : Z) : list cblk :=
    (pc_self p, P, psize p) :: (pc_buffer p, B, pc_bufalloc p)
    :: match pc_priv p with
       | PrivNg s (Some q) => [(q, I, 40 * ng_ifaces_size s)]
       | _ => []
       end.

  (* [comment removed for export] *)
  Definition pcap_wf (p : pcapT) : Prop :=
    1 <= pc_snapshot p <= INT_MAX
    /\ 0 <= pc_bufsize p <= 2^30 /\ 1 <= pc_bufalloc p < 2^32   (* [comment removed for export] *)
    /\ Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p
    /\ pc_break_loop p = 0 /\ pc_tstamp_precision p = 0
    /\ 0 <= pc_version_major p < 2^16 /\ 0 <= pc_version_minor p < 2^16
    /\ 0 <= pc_linktype p < 2^31 /\ -2^31 <= pc_linktype_ext p < 2^31
    /\ 0 <= h_caplen (pc_header p) < 2^32 /\ 0 <= h_len (pc_header p) < 2^32
    /\ match pc_priv p with
       | PrivPcap s => sf_hdrsize s = 16 \/ sf_hdrsize s = 24
       | PrivNg s _ => 0 < ng_user_tsresol s < 2^64 /\ 0 <= ng_max_blocksize s <= 2^28 /\ 0 <= ng_ifcount s < 2^32 /\ 0 <= ng_ifaces_size s < 2^32
       end
    /\ pc_bufsize p <= pc_bufalloc p.          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PCAPRg (P : Z) (p : pcapT) (PB : list cblk) (rf st os : cell) (m : mem) : Prop :=
    exists (B I : Z) (j : pcap_junk) (pad : list byte) (bs : list byte),
       PB = pcap_blocks p P B I
    /\ rw_cells asegs m P (pcap_cells_gen p P B rf st os j)
    /\ rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)
    /\ rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]
    /\ firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p)
    /\ ifaces_ok p I m
    /\ pcap_wf p.

  (* [comment removed for export] *)
  Definition PCAPR (P : Z) (p : pcapT) (PB FB : list cblk) (m : mem) : Prop :=
    exists Af, In (pc_rfile p, Af, FILE_BLOCK) FB
      /\ PCAPRg P p PB (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) m.

  (* [comment removed for export] *)
  Definition pre_PCAPR (P : Z) (p : pcapT) (PB : list cblk) (m : mem) : Prop :=
    exists rf st os, length rf = 8%nat /\ length st = 8%nat /\ length os = 8%nat /\ PCAPRg P p PB (CB 8 rf) (CB 8 st) (CB 8 os) m.

  (* [comment removed for export] *)
  Definition ifaces_closable (p : pcapT) (I : Z) (m : mem) : Prop :=
    match pc_priv p with
    | PrivPcap _ => I = 0
    | PrivNg s None => I = 0
    | PrivNg s (Some q) => (exists junk, rw_cells asegs m I [CB (Z.to_nat (40 * ng_ifaces_size s)) junk]) /\ 1 <= ng_ifaces_size s < 2^26
    end.
  Definition PCAPRg_closable (P : Z) (p : pcapT) (PB : list cblk) (rf st os : cell) (m : mem) : Prop :=
    exists (B I : Z) (j : pcap_junk) (pad : list byte) (bs : list byte),
       PB = pcap_blocks p P B I
    /\ rw_cells asegs m P (pcap_cells_gen p P B rf st os j)
    /\ rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)
    /\ rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]
    /\ firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p)
    /\ ifaces_closable p I m
    /\ pcap_wf p.
  Definition PCAPR_closable (P : Z) (p : pcapT) (PB FB : list cblk) (m : mem) : Prop :=
    exists Af, In (pc_rfile p, Af, FILE_BLOCK) FB
      /\ PCAPRg_closable P p PB (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) m.

  #[using="Type"] Lemma aln16_add : forall a k, a mod 16 = 0 -> k mod 16 = 0 -> (a + k) mod 16 = 0.
  Proof. intros a k Ha Hk. rewrite Z.add_mod, Ha, Hk by lia. reflexivity. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma rw_cells_cut : forall m A cs k,
    rw_cells asegs m A cs -> rw_cells asegs m A (firstn k cs) /\ rw_cells asegs m (A + Z.of_nat (cells_size (firstn k cs))) (skipn k cs).
  Proof. intros m A cs k HC. apply (proj1 (rw_cells_app asegs m A _ _)). rewrite firstn_skipn. exact HC. Qed.
  #[using="Type"] Lemma rw_cells_uncut : forall m A cs1 cs2 A2,
    rw_cells asegs m A cs1 -> rw_cells asegs m A2 cs2 -> A2 = A + Z.of_nat (cells_size cs1) -> rw_cells asegs m A (cs1 ++ cs2).
  Proof. intros m A cs1 cs2 A2 HC1 HC2 ->. apply (proj2 (rw_cells_app asegs m A _ _)). split; assumption. Qed.
  Definition set_pj_g (g : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) (pj_f j) g (pj_h j) (pj_breakloop j).
  Definition set_pj_f (f : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) f (pj_g j) (pj_h j) (pj_breakloop j).
  Definition set_pj_h (h : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) (pj_f j) (pj_g j) h (pj_breakloop j).
  #[using="Type"] Remark pc_pre_size : forall p P B rf j, csize rf = 8%nat -> cells_size (pc_pre p P B rf j) = 216%nat.
  Proof. intros p P B rf j Hrf. cbn. rewrite Hrf. reflexivity. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma pcap_cells_split4 : forall m P p B rf st os j,
    csize rf = 8%nat ->
    rw_cells asegs m P (pcap_cells_gen p P B rf st os j) ->
    rw_cells asegs m P (pc_pre p P B rf j) /\ rw_cells asegs m (P + 216) [CB 304 (pj_g j)]
    /\ rw_cells asegs m (P + 520) (hdr_cells (pc_header p)) /\ rw_cells asegs m (P + 544) (pc_ops p st os j).
  Proof.
    intros m P p B rf st os j Hrf HC. unfold pcap_cells_gen in HC.
    apply rw_cells_app in HC as [H1 HC]. rewrite (pc_pre_size p P B rf j Hrf) in HC.
    apply rw_cells_app in HC as [H2 HC]. cbn [cells_size csize Nat.add] in HC.
    apply rw_cells_app in HC as [H3 H4]. cbn [cells_size csize Nat.add hdr_cells] in H4.
    replace (P + Z.of_nat 216 + Z.of_nat 304 + Z.of_nat 24) with (P + 544) in H4 by lia.
    replace (P + Z.of_nat 216 + Z.of_nat 304) with (P + 520) in H3 by lia.
    replace (P + Z.of_nat 216) with (P + 216) in H2 by lia. auto.
  Qed.
  #[using="Type"] Lemma pcap_cells_join4 : forall m P p B rf st os j cs h,
    csize rf = 8%nat ->
    rw_cells asegs m P (pc_pre p P B rf j) -> rw_cells asegs m (P + 216) cs -> cells_size cs = 304%nat ->
    rw_cells asegs m (P + 520) (hdr_cells h) -> rw_cells asegs m (P + 544) (pc_ops p st os j) ->
    rw_cells asegs m P (pcap_cells_gen (set_header h p) P B rf st os (set_pj_g (cells_bytes cs) j)).
  Proof.
    intros m P p B rf st os j cs h Hrf H1 H2 Hcs H3 H4. unfold pcap_cells_gen.
    assert (E1 : pc_pre (set_header h p) P B rf (set_pj_g (cells_bytes cs) j) = pc_pre p P B rf j).
    { unfold pc_pre, np_entry, is_ng. destruct p; reflexivity. }
    assert (E2 : pc_ops (set_header h p) st os (set_pj_g (cells_bytes cs) j) = pc_ops p st os j).
    { unfold pc_ops, cleanup_entry, is_ng. destruct p; reflexivity. }
    rewrite E1, E2. replace (pc_header (set_header h p)) with h by (destruct p; reflexivity). cbn [pj_g set_pj_g].
    apply rw_cells_app. split; [exact H1|]. rewrite (pc_pre_size p P B rf j Hrf).
    pose proof (rw_cells_merge asegs m (P + 216) [] cs (hdr_cells h ++ pc_ops p st os j)) as M. cbn [app] in M. rewrite Hcs in M.
    replace (P + Z.of_nat 216) with (P + 216) by lia. apply M.
    apply rw_cells_app. split; [exact H2|]. rewrite Hcs. apply rw_cells_app. split.
    - replace (P + 216 + Z.of_nat 304) with (P + 520) by lia. exact H3.
    - cbn [cells_size csize hdr_cells Nat.add]. replace (P + 216 + Z.of_nat 304 + Z.of_nat 24) with (P + 544) by lia. exact H4.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma rw_cells_recell : forall m A cs cs',
    rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
  Proof.
    intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf'| rewrite Heq; exact Hb]|].
    rewrite <- (cells_bytes_length cs' Hwf'), Heq, (cells_bytes_length cs Hwf). exact Hw.
  Qed.
  (* [comment removed for export] *)
  Definition pack2 (lo hi : word) : word := Z_to_bv 64 (bv_unsigned lo mod 2^32 + 2^32 * (bv_unsigned hi mod 2^32)).
  Definition hdr3 (h : pkthdr) : list cell :=
    [C8 (Z_to_bv 64 (h_sec h)); C8 (Z_to_bv 64 (h_usec h)); C8 (pack2 (Z_to_bv 64 (h_caplen h)) (Z_to_bv 64 (h_len h)))].
  #[using="Type"] Lemma Z_to_le_bytes_split : forall a b z, (0 <= z)%Z ->
    Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
  Proof.
    induction a as [|a IH]; intros b z Hz.
    - cbn [Nat.add app Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
    - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH by (apply Z.shiftr_nonneg; lia). f_equal. f_equal.
      rewrite Z.shiftr_shiftr by lia. f_equal. lia.
  Qed.
  #[using="Type"] Lemma le8_pack2 : forall lo hi, le8 (pack2 lo hi) = le4 lo ++ le4 hi.
  Proof.
    intros lo hi. unfold pack2, le8, le4, word_to_le_bytes.
    pose proof (Z.mod_pos_bound (bv_unsigned lo) (2^32) ltac:(lia)) as H1.
    pose proof (Z.mod_pos_bound (bv_unsigned hi) (2^32) ltac:(lia)) as H2.
    rewrite unsigned_lit by lia. change 8%nat with (4 + 4)%nat at 1. rewrite Z_to_le_bytes_split by lia. f_equal.
    - rewrite <- (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned lo) 32) by (cbn; lia). f_equal.
      rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
    - rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned hi) 32) by (cbn; lia). f_equal.
      change (8 * Z.of_nat 4)%Z with 32%Z. rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma hdr3_bytes : forall h, cells_bytes (hdr3 h) = cells_bytes (hdr_cells h).
  Proof. intros h. cbn [cells_bytes cbytes hdr3 hdr_cells]. rewrite le8_pack2, <- app_assoc. reflexivity. Qed.
  #[using="Type"] Lemma hdr_cells_to_3 : forall m A h, rw_cells asegs m A (hdr_cells h) -> rw_cells asegs m A (hdr3 h).
  Proof. intros m A h HC. eapply rw_cells_recell; [exact HC| cbn; repeat split; exact I | apply hdr3_bytes]. Qed.
  #[using="Type"] Lemma hdr_cells_of_3 : forall m A h, rw_cells asegs m A (hdr3 h) -> rw_cells asegs m A (hdr_cells h).
  Proof. intros m A h HC. eapply rw_cells_recell; [exact HC| cbn; repeat split; exact I | symmetry; apply hdr3_bytes]. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma PCAPRg_blocks : forall P p PB rf st os m, PCAPRg P p PB rf st os m ->
    exists B I, PB = pcap_blocks p P B I.
  Proof. intros P p PB rf st os m (B & I & j & pad & bs & E & _). exists B, I. exact E. Qed.
  #[using="Type"] Lemma PCAPR_self_in : forall P p PB FB m, PCAPR P p PB FB m -> In (pc_self p, P, psize p) PB.
  Proof. intros P p PB FB m (Af & _ & (B & I & j & pad & bs & -> & _)). left. reflexivity. Qed.
  #[using="Type"] Lemma psize_pos : forall p, 664 <= psize p <= 680.
  Proof. intros p. unfold psize, PCAP_NG_SF_TOTAL, PCAP_SF_TOTAL. destruct (is_ng p); lia. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma priv_cells_size : forall p I pad, length pad = 4%nat ->
    cells_size (priv_cells p I pad) = (if is_ng p then 32 else 16)%nat.
  Proof. intros p I pad Hp. unfold priv_cells, is_ng. destruct (pc_priv p); cbn; reflexivity. Qed.
  #[using="Type"] Lemma priv_cells_size_le : forall m P p I pad, rw_cells asegs m P (priv_cells p I pad) -> (Z.of_nat (cells_size (priv_cells p I pad)) <= 32)%Z.
  Proof.
    intros m P p I pad [[Hwf _] _]. unfold priv_cells in *. destruct (pc_priv p); cbn in *; [lia|].
    destruct Hwf as (_ & _ & _ & _ & Hl & _). cbn in Hl. lia.
  Qed.
  #[using="Type"] Lemma if_cells_size : forall i j, cells_size (if_cells i j) = 40%nat.
  Proof. intros. reflexivity. Qed.
  #[using="Type"] Lemma ifs_cells_size : forall ifs js, length js = length ifs -> cells_size (ifs_cells ifs js) = (40 * length ifs)%nat.
  Proof.
    induction ifs as [|i ifs IH]; intros [|j0 js0] Hlen; cbn [length] in Hlen; try discriminate Hlen.
    - reflexivity.
    - cbn [ifs_cells]. rewrite cells_size_app, if_cells_size, (IH js0) by lia. cbn [length]. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma ifaces_ok_agree : forall p I m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    ifaces_ok p I m -> ifaces_ok p I m'.
  Proof.
    intros p I m m' Q AG HQ IFS. unfold ifaces_ok in *. destruct (pc_priv p) as [sf|sg [q|]] eqn:E; try exact IFS.
    destruct IFS as (js & tail & Hl & HC & H1 & H2 & H3 & H4). exists js, tail. split; [exact Hl|]. split; [|repeat split; try assumption; lia].
    eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. apply (HQ sg q eq_refl).
    pose proof (rw_cells_bound _ _ _ _ HC) as HB.
    rewrite cells_size_app in Ha, HB. cbn [cells_size csize] in Ha, HB. rewrite Nat.add_0_r in Ha, HB.
    rewrite ifs_cells_size in Ha by (rewrite length_rev; lia). rewrite length_rev in Ha. lia.
  Qed.
  #[using="Type"] Lemma priv_cells_psize : forall m A p I pad, rw_cells asegs m A (priv_cells p I pad) ->
    Z.of_nat (cells_size (priv_cells p I pad)) = psize p - PCAP_PRIV_OFF.
  Proof.
    intros m A p I pad [[Hwf _] _]. unfold priv_cells, psize, is_ng, PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL, PCAP_SF_TOTAL in *.
    destruct (pc_priv p); cbn in *; lia.
  Qed.
  #[using="Type"] Lemma pcap_aux_agree : forall p P B I pad bs m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall a, B <= a < B + pc_bufalloc p -> Q a) ->
    (forall a, P + PCAP_PRIV_OFF <= a < P + psize p -> Q a) ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    0 <= pc_bufalloc p ->
    rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> ifaces_ok p I m ->
    rw_cells asegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ rw_cells asegs m' (P + PCAP_PRIV_OFF) (priv_cells p I pad) /\ ifaces_ok p I m'.
  Proof.
    intros p P B I pad bs m m' Q AG HB HP HI Hba BUF PRIV IFS. split; [|split].
    - eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply HB. cbn [cells_size csize] in Ha. lia.
    - eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply HP. pose proof (priv_cells_psize _ _ _ _ _ PRIV). lia.
    - eapply ifaces_ok_agree; eassumption.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma pcap_cells_gen_size : forall p P B rf st os j, csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    cells_size (pcap_cells_gen p P B rf st os j) = 648%nat.
  Proof. intros p P B rf st os j H1 H2 H3. unfold pcap_cells_gen. rewrite !cells_size_app. cbn. rewrite H1, H2, H3. reflexivity. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma PCAPRg_agree : forall P p PB rf st os m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    PCAPRg P p PB rf st os m -> PCAPRg P p PB rf st os m'.
  Proof.
    intros P p PB rf st os m m' Q AG HQ Hrf Hst Hos (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF).
    exists B, I, j, pad, bs. split; [exact EPB|].
    pose proof (psize_pos p) as PS. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ. unfold PCAP_PRIV_OFF in PZ.
    pose proof WF as (_ & _ & W3 & _).
    assert (Q1 : forall a, P <= a < P + psize p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q2 : forall a, B <= a < B + pc_bufalloc p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q3 : forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a).
    { intros sg q Hq a Ha. apply HQ. rewrite EPB. unfold pcap_blocks. rewrite Hq. unfold in_block.
      do 2 apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    split. { eapply agrees_rw_cells; [exact AG|exact CELLS|]. intros a Ha. rewrite (pcap_cells_gen_size p P B rf st os j Hrf Hst Hos) in Ha. apply Q1. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply Q1. unfold PCAP_PRIV_OFF in Ha. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply Q2. cbn [cells_size csize] in Ha. lia. }
    split; [exact PFX|]. split; [|exact WF]. eapply ifaces_ok_agree; [exact AG| exact Q3| exact IFS].
  Qed.
  #[using="Type"] Lemma PCAPR_agree : forall P p PB FB m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> PCAPR P p PB FB m -> PCAPR P p PB FB m'.
  Proof.
    intros P p PB FB m m' Q AG HQ (Af & Hin & PG). exists Af. split; [exact Hin|].
    eapply PCAPRg_agree; [exact AG|exact HQ|reflexivity|reflexivity|reflexivity|exact PG].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma ifaces_ok_closable : forall p I m, ifaces_ok p I m -> ifaces_closable p I m.
  Proof.
    intros p I m HI. unfold ifaces_ok, ifaces_closable in *. destruct (pc_priv p) as [sf|s [q|]]; [exact HI| |tauto].
    destruct HI as (js & tail & Ljs & CE & E1 & E2 & E3 & E4). split; [|exact E3].
    rewrite <- (app_nil_r [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) tail]), app_assoc in CE.
    apply (rw_cells_merge asegs m I [] _ []) in CE. cbn [app] in CE. rewrite cells_size_app, ifs_cells_size in CE by (rewrite length_rev; lia).
    cbn [cells_size csize Nat.add] in CE. rewrite length_rev in CE.
    replace (40 * length (ng_ifaces s) + (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s)) + 0))%nat with (Z.to_nat (40 * ng_ifaces_size s)) in CE by lia.
    eexists. exact CE.
  Qed.
  #[using="Type"] Lemma PCAPR_closable_of : forall P p PB FB m, PCAPR P p PB FB m -> PCAPR_closable P p PB FB m.
  Proof.
    intros P p PB FB m (Af & Hin & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    exists Af. split; [exact Hin|]. exists B, I, j, pad, bs. repeat (split; [assumption|]). split; [apply ifaces_ok_closable; exact IFS| exact WF].
  Qed.
  #[using="Type"] Lemma ifaces_closable_agree : forall p I m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    ifaces_closable p I m -> ifaces_closable p I m'.
  Proof.
    intros p I m m' Q AG HQ IFS. unfold ifaces_closable in *. destruct (pc_priv p) as [sf|sg [q|]] eqn:E; try exact IFS.
    destruct IFS as ((junk & HC) & H3). split; [|exact H3]. exists junk.
    eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. apply (HQ sg q eq_refl). cbn [cells_size csize] in Ha. lia.
  Qed.
  #[using="Type"] Lemma PCAPRg_closable_agree : forall P p PB rf st os m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    PCAPRg_closable P p PB rf st os m -> PCAPRg_closable P p PB rf st os m'.
  Proof.
    intros P p PB rf st os m m' Q AG HQ Hrf Hst Hos (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF).
    exists B, I, j, pad, bs. split; [exact EPB|].
    pose proof (psize_pos p) as PS. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ. unfold PCAP_PRIV_OFF in PZ.
    pose proof WF as (_ & _ & W3 & _).
    assert (Q1 : forall a, P <= a < P + psize p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q2 : forall a, B <= a < B + pc_bufalloc p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q3 : forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a).
    { intros sg q Hq a Ha. apply HQ. rewrite EPB. unfold pcap_blocks. rewrite Hq. unfold in_block.
      do 2 apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    split. { eapply agrees_rw_cells; [exact AG|exact CELLS|]. intros a Ha. rewrite (pcap_cells_gen_size p P B rf st os j Hrf Hst Hos) in Ha. apply Q1. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply Q1. unfold PCAP_PRIV_OFF in Ha. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply Q2. cbn [cells_size csize] in Ha. lia. }
    split; [exact PFX|]. split; [|exact WF]. eapply ifaces_closable_agree; [exact AG| exact Q3| exact IFS].
  Qed.
  #[using="Type"] Lemma PCAPR_closable_agree : forall P p PB FB m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> PCAPR_closable P p PB FB m -> PCAPR_closable P p PB FB m'.
  Proof.
    intros P p PB FB m m' Q AG HQ (Af & Hin & PG). exists Af. split; [exact Hin|].
    eapply PCAPRg_closable_agree; [exact AG|exact HQ|reflexivity|reflexivity|reflexivity|exact PG].
  Qed.
  #[using="Type"] Lemma pcap_wf_set_header : forall p h, pcap_wf p -> 0 <= h_caplen h < 2^32 -> 0 <= h_len h < 2^32 -> pcap_wf (set_header h p).
  Proof. intros p h WF Hc Hl. unfold pcap_wf in *. destruct p; cbn in *. repeat split; try lia; tauto. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma PCAPR_intro_set_header : forall P p PB FB m h Af B I j pad bs,
    In (pc_rfile p, Af, FILE_BLOCK) FB -> PB = pcap_blocks p P B I ->
    rw_cells asegs m P (pcap_cells_gen (set_header h p) P B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j) ->
    rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
    firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) -> ifaces_ok p I m -> pcap_wf p ->
    0 <= h_caplen h < 2^32 -> 0 <= h_len h < 2^32 ->
    PCAPR P (set_header h p) PB FB m.
  Proof.
    intros P p PB FB m h Af B I j pad bs Hin EPB HC HP HB PFX IFS WF Hc Hl.
    pose proof (pcap_wf_set_header p h WF Hc Hl) as WF'.
    exists Af. split; [destruct p; exact Hin|]. exists B, I, j, pad, bs.
    split; [destruct p; exact EPB|]. split; [exact HC|]. split; [destruct p; exact HP|]. split; [destruct p; exact HB|].
    split; [destruct p; exact PFX|]. split; [destruct p; exact IFS| exact WF'].
  Qed.
End Rep.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ceil_facts := idtac.

Record pcap_consts := mkPK {
  pk_next_pcap : Z;     (* [comment removed for export] *)
  pk_next_ng : Z;       (* [comment removed for export] *)
  pk_cleanup_sf : Z;    (* [comment removed for export] *)
  pk_cleanup_ng : Z;    (* [comment removed for export] *)
  pk_oneshot : Z;       (* [comment removed for export] *)
  pk_stats : Z          (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition PK : pcap_consts := mkPK 0x885a0 0x8ccf0 0x84ccc 0x8e018 0x85a0c 0x85934.

Definition PCAP_NEXT_EX_ENTRY : Z := 0x85ac0.
Definition PCAP_OFFLINE_READ_ENTRY : Z := 0x854d0.
Definition PCAP_STATS_ENTRY : Z := 0x86054.
Definition PCAP_CLOSE_ENTRY : Z := 0x85d7c.
Definition PCAP_FREECODE_ENTRY : Z := 0x85970.
Definition PCAP_OPEN_OFFLINE_ENTRY : Z := 0x854ac.
Definition PCAP_OPEN_OFFLINE_WTP_ENTRY : Z := 0x84d84.
Definition PCAP_FOPEN_OFFLINE_WTP_ENTRY : Z := 0x84f40.
Definition PCAP_OPEN_OFFLINE_COMMON_ENTRY : Z := 0x85e2c.
Definition PCAP_CHECK_HEADER_ENTRY : Z := 0x87afc.
Definition PCAP_NG_CHECK_HEADER_ENTRY : Z := 0x8ac1c.
Definition PCAP_ADJUST_SNAPSHOT_ENTRY : Z := 0x854b8.
Definition LINKTYPE_TO_DLT_ENTRY : Z := 0x893ac.
Definition MAX_SNAPLEN_ENTRY : Z := 0x89424.
Definition PCAP_POST_PROCESS_ENTRY : Z := 0x8945c.
Definition PCAP_STRERROR_ENTRY : Z := 0x85fa8.
Definition PCAP_FMT_ERRMSG_ENTRY : Z := 0x86100.
Definition READ_BYTES_ENTRY : Z := 0x8b9d4.
Definition READ_BLOCK_ENTRY : Z := 0x8baf0.
Definition ADD_INTERFACE_ENTRY : Z := 0x8c2d8.
Definition FILE_BLOCK : Z := 1264.    (* [comment removed for export] *)
Definition PCAP_HDR_OFF : Z := 520.   (* [comment removed for export] *)
Definition PCAP_ERRBUF_OFF : Z := 216.
Definition PCAP_PRIV_OFF : Z := 648.  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma eqz_false : forall z, (0 < z < 2^64)%Z -> bv_eqb (Z_to_bv 64 z) z64 = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.
Lemma nez_true : forall z, (0 < z < 2^64)%Z -> negb (bv_eqb (Z_to_bv 64 z) z64) = true.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. Qed.
Lemma eqb_lits_false : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y Hx Hy Hne. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact Hne. Qed.

(* [comment removed for export] *)
Lemma and7_aligned : forall x, (0 <= x < 2^64)%Z -> (x mod 8 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0%Z.
Proof.
  intros x Hx Ha. rewrite unsigned_lit by lia. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Ha.
Qed.
Lemma and3_aligned : forall x, (0 <= x < 2^64)%Z -> (x mod 4 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 x)) 3 = 0%Z.
Proof.
  intros x Hx Ha. rewrite unsigned_lit by lia. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2)%Z with 4%Z. exact Ha.
Qed.
Lemma aligned16_8 : forall x k, (x mod 16 = 0)%Z -> (k mod 8 = 0)%Z -> ((x + k) mod 8 = 0)%Z.
Proof.
  intros x k Hx Hk. rewrite Z.add_mod, Hk, Z.add_0_r by lia. rewrite Z.mod_mod by lia.
  apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->]. replace (q * 16)%Z with ((q * 2) * 8)%Z by lia. apply Z.mod_mul.
  all: lia.
Qed.
Section Rep.
  Context {CEILV : Ceiling.CEIL} {H hptr : Type} (HO : HeapOps H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).

  Definition b8 (z : Z) : byte := Z_to_bv 8 z.

  Definition is_ng (p : pcapT) : bool := match pc_priv p with PrivNg _ _ => true | PrivPcap _ => false end.
  Definition np_entry (p : pcapT) : Z := if is_ng p then pk_next_ng PK else pk_next_pcap PK.
  Definition cleanup_entry (p : pcapT) : Z := if is_ng p then pk_cleanup_ng PK else pk_cleanup_sf PK.
  (* [comment removed for export] *)
  Definition psize (p : pcapT) : Z := if is_ng p then PCAP_NG_SF_TOTAL else PCAP_SF_TOTAL.

  (* [comment removed for export] *)
  Definition hdr_cells (h : pkthdr) : list cell :=
    [C8 (Z_to_bv 64 (h_sec h)); C8 (Z_to_bv 64 (h_usec h)); C4 (Z_to_bv 64 (h_caplen h)); C4 (Z_to_bv 64 (h_len h))].

  (* [comment removed for export] *)
  Record pcap_junk := mkPJ {
    pj_read_op : word;      (* [comment removed for export] *)
    pj_fd : word;           (* [comment removed for export] *)
    pj_a : list byte;       (* [comment removed for export] *)
    pj_b : list byte;       (* [comment removed for export] *)
    pj_c : list byte;       (* [comment removed for export] *)
    pj_d : list byte;       (* [comment removed for export] *)
    pj_e : list byte;       (* [comment removed for export] *)
    pj_f : list byte;       (* [comment removed for export] *)
    pj_g : list byte;       (* [comment removed for export] *)
    pj_h : list byte;       (* [comment removed for export] *)
    pj_breakloop : word     (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pc_pre (p : pcapT) (P B : Z) (rf : cell) (j : pcap_junk) : list cell :=
    [ C8 (pj_read_op j);                         (* [comment removed for export] *)
      C8 (Z_to_bv 64 (np_entry p));              (* [comment removed for export] *)
      C4 (pj_fd j);                              (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_bufsize p));            (* [comment removed for export] *)
      C8 (Z_to_bv 64 B);                         (* [comment removed for export] *)
      CB 12 (pj_a j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_break_loop p));         (* [comment removed for export] *)
      C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF));       (* [comment removed for export] *)
      C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)));    (* [comment removed for export] *)
      CB 4 (pj_b j);                             (* [comment removed for export] *)
      rf;                                        (* [comment removed for export] *)
      CB 16 (pj_c j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_version_major p));      (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_version_minor p));      (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_snapshot p));           (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_linktype p));           (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_linktype_ext p));       (* [comment removed for export] *)
      CB 12 (pj_d j);                            (* [comment removed for export] *)
      C8 (Z_to_bv 64 0);                         (* [comment removed for export] *)
      CB 28 (pj_e j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_tstamp_precision p));   (* [comment removed for export] *)
      CB 48 (pj_f j);                            (* [comment removed for export] *)
      C8 (Z_to_bv 64 0) ].                       (* [comment removed for export] *)
  Definition pc_ops (p : pcapT) (st os : cell) (j : pcap_junk) : list cell :=
    [ CB 72 (pj_h j);                            (* [comment removed for export] *)
      st;                                        (* [comment removed for export] *)
      C8 (pj_breakloop j);                       (* [comment removed for export] *)
      os;                                        (* [comment removed for export] *)
      C8 (Z_to_bv 64 (cleanup_entry p)) ].       (* [comment removed for export] *)
  Definition pcap_cells_gen (p : pcapT) (P B : Z) (rf st os : cell) (j : pcap_junk) : list cell :=
    pc_pre p P B rf j ++ [CB 304 (pj_g j)] (* [comment removed for export] *) ++ hdr_cells (pc_header p) (* [comment removed for export] *) ++ pc_ops p st os j.

  Definition pcap_cells (p : pcapT) (P B Af : Z) (j : pcap_junk) : list cell :=
    pcap_cells_gen p P B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j.

  #[using="Type"] Remark pcap_cells_size : forall p P B Af j, cells_size (pcap_cells p P B Af j) = 648%nat.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition lenswap_code (l : lenswap_t) : Z := match l with NOT_SWAPPED => 0 | SWAPPED => 1 | MAYBE_SWAPPED => 2 end.
  Definition sfscale_code (t : sf_scale_t) : Z := match t with SF_PASS_THROUGH => 0 | SF_SCALE_UP => 1 | SF_SCALE_DOWN => 2 end.
  Definition ngscale_code (t : ng_scale_t) : Z :=
    match t with NG_PASS_THROUGH => 0 | SCALE_UP_DEC => 1 | SCALE_DOWN_DEC => 2 | SCALE_UP_BIN => 3 | SCALE_DOWN_BIN => 4 end.
  Definition is_dec (t : ng_scale_t) : bool := match t with SCALE_UP_DEC | SCALE_DOWN_DEC => true | _ => false end.

  (* [comment removed for export] *)
  Definition sf_cells (s : pcap_sf) : list cell :=
    [C8 (Z_to_bv 64 (sf_hdrsize s)); C4 (Z_to_bv 64 (lenswap_code (sf_lengths_swapped s))); C4 (Z_to_bv 64 (sfscale_code (sf_scale_type s)))].
  (* [comment removed for export] *)
  Definition ng_cells (s : pcap_ng_sf) (I : Z) (pad : list byte) : list cell :=
    [C8 (Z_to_bv 64 (ng_user_tsresol s)); C4 (Z_to_bv 64 (ng_max_blocksize s)); C4 (Z_to_bv 64 (ng_ifcount s));
     C4 (Z_to_bv 64 (ng_ifaces_size s)); CB 4 pad; C8 (Z_to_bv 64 I)].
  Definition priv_cells (p : pcapT) (I : Z) (pad : list byte) : list cell :=
    match pc_priv p with PrivPcap s => sf_cells s | PrivNg s _ => ng_cells s I pad end.

  (* [comment removed for export] *)
  Record if_junk := mkIJ { ij_p1 : list byte; ij_p2 : list byte; ij_sf : word }.
  Definition if_cells (i : ng_if) (j : if_junk) : list cell :=
    [C4 (Z_to_bv 64 (if_snaplen i)); CB 4 (ij_p1 j); C8 (Z_to_bv 64 (if_tsresol i)); C4 (Z_to_bv 64 (ngscale_code (if_scale_type i)));
     CB 4 (ij_p2 j); C8 (if is_dec (if_scale_type i) then Z_to_bv 64 (if_scale_factor i) else ij_sf j); C8 (Z_to_bv 64 (if_tsoffset i))].
  Fixpoint ifs_cells (ifs : list ng_if) (js : list if_junk) : list cell :=
    match ifs, js with
    | i :: ifs', j :: js' => if_cells i j ++ ifs_cells ifs' js'
    | _, _ => []
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition if_wf (i : ng_if) : Prop :=
    0 < if_tsresol i < 2^64 /\ (is_dec (if_scale_type i) = true -> 0 < if_scale_factor i < 2^64).

  Definition ifaces_ok (p : pcapT) (I : Z) (m : mem) : Prop :=
    match pc_priv p with
    | PrivPcap _ => I = 0
    | PrivNg s None => I = 0 /\ ng_ifaces s = [] /\ ng_ifcount s = 0 /\ ng_ifaces_size s = 0
    | PrivNg s (Some q) =>
        exists js tail, length js = length (ng_ifaces s)
          /\ rw_cells asegs m I (ifs_cells (rev (ng_ifaces s)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) tail])
          /\ ng_ifcount s = Z.of_nat (length (ng_ifaces s)) /\ ng_ifcount s <= ng_ifaces_size s /\ 1 <= ng_ifaces_size s < 2^26
          /\ Forall if_wf (ng_ifaces s)
    end.

  (* [comment removed for export] *)
  Definition pcap_blocks (p : pcapT) (P B I : Z) : list cblk :=
    (pc_self p, P, psize p) :: (pc_buffer p, B, pc_bufalloc p)
    :: match pc_priv p with
       | PrivNg s (Some q) => [(q, I, 40 * ng_ifaces_size s)]
       | _ => []
       end.

  (* [comment removed for export] *)
  Definition pcap_wf (p : pcapT) : Prop :=
    1 <= pc_snapshot p <= INT_MAX
    /\ 0 <= pc_bufsize p <= 2^30 /\ 1 <= pc_bufalloc p < 2^32   (* [comment removed for export] *)
    /\ Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p
    /\ pc_break_loop p = 0 /\ pc_tstamp_precision p = 0
    /\ 0 <= pc_version_major p < 2^16 /\ 0 <= pc_version_minor p < 2^16
    /\ 0 <= pc_linktype p < 2^31 /\ -2^31 <= pc_linktype_ext p < 2^31
    /\ 0 <= h_caplen (pc_header p) < 2^32 /\ 0 <= h_len (pc_header p) < 2^32
    /\ match pc_priv p with
       | PrivPcap s => sf_hdrsize s = 16 \/ sf_hdrsize s = 24
       | PrivNg s _ => 0 < ng_user_tsresol s < 2^64 /\ 0 <= ng_max_blocksize s <= 2^28 /\ 0 <= ng_ifcount s < 2^32 /\ 0 <= ng_ifaces_size s < 2^32
       end
    /\ pc_bufsize p <= pc_bufalloc p.          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PCAPRg (P : Z) (p : pcapT) (PB : list cblk) (rf st os : cell) (m : mem) : Prop :=
    exists (B I : Z) (j : pcap_junk) (pad : list byte) (bs : list byte),
       PB = pcap_blocks p P B I
    /\ rw_cells asegs m P (pcap_cells_gen p P B rf st os j)
    /\ rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)
    /\ rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]
    /\ firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p)
    /\ ifaces_ok p I m
    /\ pcap_wf p.

  (* [comment removed for export] *)
  Definition PCAPR (P : Z) (p : pcapT) (PB FB : list cblk) (m : mem) : Prop :=
    exists Af, In (pc_rfile p, Af, FILE_BLOCK) FB
      /\ PCAPRg P p PB (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) m.

  (* [comment removed for export] *)
  Definition pre_PCAPR (P : Z) (p : pcapT) (PB : list cblk) (m : mem) : Prop :=
    exists rf st os, length rf = 8%nat /\ length st = 8%nat /\ length os = 8%nat /\ PCAPRg P p PB (CB 8 rf) (CB 8 st) (CB 8 os) m.

  (* [comment removed for export] *)
  Definition ifaces_closable (p : pcapT) (I : Z) (m : mem) : Prop :=
    match pc_priv p with
    | PrivPcap _ => I = 0
    | PrivNg s None => I = 0
    | PrivNg s (Some q) => (exists junk, rw_cells asegs m I [CB (Z.to_nat (40 * ng_ifaces_size s)) junk]) /\ 1 <= ng_ifaces_size s < 2^26
    end.
  Definition PCAPRg_closable (P : Z) (p : pcapT) (PB : list cblk) (rf st os : cell) (m : mem) : Prop :=
    exists (B I : Z) (j : pcap_junk) (pad : list byte) (bs : list byte),
       PB = pcap_blocks p P B I
    /\ rw_cells asegs m P (pcap_cells_gen p P B rf st os j)
    /\ rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)
    /\ rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]
    /\ firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p)
    /\ ifaces_closable p I m
    /\ pcap_wf p.
  Definition PCAPR_closable (P : Z) (p : pcapT) (PB FB : list cblk) (m : mem) : Prop :=
    exists Af, In (pc_rfile p, Af, FILE_BLOCK) FB
      /\ PCAPRg_closable P p PB (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) m.

  #[using="Type"] Lemma aln16_add : forall a k, a mod 16 = 0 -> k mod 16 = 0 -> (a + k) mod 16 = 0.
  Proof. intros a k Ha Hk. rewrite Z.add_mod, Ha, Hk by lia. reflexivity. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma rw_cells_cut : forall m A cs k,
    rw_cells asegs m A cs -> rw_cells asegs m A (firstn k cs) /\ rw_cells asegs m (A + Z.of_nat (cells_size (firstn k cs))) (skipn k cs).
  Proof. intros m A cs k HC. apply (proj1 (rw_cells_app asegs m A _ _)). rewrite firstn_skipn. exact HC. Qed.
  #[using="Type"] Lemma rw_cells_uncut : forall m A cs1 cs2 A2,
    rw_cells asegs m A cs1 -> rw_cells asegs m A2 cs2 -> A2 = A + Z.of_nat (cells_size cs1) -> rw_cells asegs m A (cs1 ++ cs2).
  Proof. intros m A cs1 cs2 A2 HC1 HC2 ->. apply (proj2 (rw_cells_app asegs m A _ _)). split; assumption. Qed.
  Definition set_pj_g (g : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) (pj_f j) g (pj_h j) (pj_breakloop j).
  Definition set_pj_f (f : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) f (pj_g j) (pj_h j) (pj_breakloop j).
  Definition set_pj_h (h : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) (pj_f j) (pj_g j) h (pj_breakloop j).
  #[using="Type"] Remark pc_pre_size : forall p P B rf j, csize rf = 8%nat -> cells_size (pc_pre p P B rf j) = 216%nat.
  Proof. intros p P B rf j Hrf. cbn. rewrite Hrf. reflexivity. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma pcap_cells_split4 : forall m P p B rf st os j,
    csize rf = 8%nat ->
    rw_cells asegs m P (pcap_cells_gen p P B rf st os j) ->
    rw_cells asegs m P (pc_pre p P B rf j) /\ rw_cells asegs m (P + 216) [CB 304 (pj_g j)]
    /\ rw_cells asegs m (P + 520) (hdr_cells (pc_header p)) /\ rw_cells asegs m (P + 544) (pc_ops p st os j).
  Proof.
    intros m P p B rf st os j Hrf HC. unfold pcap_cells_gen in HC.
    apply rw_cells_app in HC as [H1 HC]. rewrite (pc_pre_size p P B rf j Hrf) in HC.
    apply rw_cells_app in HC as [H2 HC]. cbn [cells_size csize Nat.add] in HC.
    apply rw_cells_app in HC as [H3 H4]. cbn [cells_size csize Nat.add hdr_cells] in H4.
    replace (P + Z.of_nat 216 + Z.of_nat 304 + Z.of_nat 24) with (P + 544) in H4 by lia.
    replace (P + Z.of_nat 216 + Z.of_nat 304) with (P + 520) in H3 by lia.
    replace (P + Z.of_nat 216) with (P + 216) in H2 by lia. auto.
  Qed.
  #[using="Type"] Lemma pcap_cells_join4 : forall m P p B rf st os j cs h,
    csize rf = 8%nat ->
    rw_cells asegs m P (pc_pre p P B rf j) -> rw_cells asegs m (P + 216) cs -> cells_size cs = 304%nat ->
    rw_cells asegs m (P + 520) (hdr_cells h) -> rw_cells asegs m (P + 544) (pc_ops p st os j) ->
    rw_cells asegs m P (pcap_cells_gen (set_header h p) P B rf st os (set_pj_g (cells_bytes cs) j)).
  Proof.
    intros m P p B rf st os j cs h Hrf H1 H2 Hcs H3 H4. unfold pcap_cells_gen.
    assert (E1 : pc_pre (set_header h p) P B rf (set_pj_g (cells_bytes cs) j) = pc_pre p P B rf j).
    { unfold pc_pre, np_entry, is_ng. destruct p; reflexivity. }
    assert (E2 : pc_ops (set_header h p) st os (set_pj_g (cells_bytes cs) j) = pc_ops p st os j).
    { unfold pc_ops, cleanup_entry, is_ng. destruct p; reflexivity. }
    rewrite E1, E2. replace (pc_header (set_header h p)) with h by (destruct p; reflexivity). cbn [pj_g set_pj_g].
    apply rw_cells_app. split; [exact H1|]. rewrite (pc_pre_size p P B rf j Hrf).
    pose proof (rw_cells_merge asegs m (P + 216) [] cs (hdr_cells h ++ pc_ops p st os j)) as M. cbn [app] in M. rewrite Hcs in M.
    replace (P + Z.of_nat 216) with (P + 216) by lia. apply M.
    apply rw_cells_app. split; [exact H2|]. rewrite Hcs. apply rw_cells_app. split.
    - replace (P + 216 + Z.of_nat 304) with (P + 520) by lia. exact H3.
    - cbn [cells_size csize hdr_cells Nat.add]. replace (P + 216 + Z.of_nat 304 + Z.of_nat 24) with (P + 544) by lia. exact H4.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma rw_cells_recell : forall m A cs cs',
    rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
  Proof.
    intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf'| rewrite Heq; exact Hb]|].
    rewrite <- (cells_bytes_length cs' Hwf'), Heq, (cells_bytes_length cs Hwf). exact Hw.
  Qed.
  (* [comment removed for export] *)
  Definition pack2 (lo hi : word) : word := Z_to_bv 64 (bv_unsigned lo mod 2^32 + 2^32 * (bv_unsigned hi mod 2^32)).
  Definition hdr3 (h : pkthdr) : list cell :=
    [C8 (Z_to_bv 64 (h_sec h)); C8 (Z_to_bv 64 (h_usec h)); C8 (pack2 (Z_to_bv 64 (h_caplen h)) (Z_to_bv 64 (h_len h)))].
  #[using="Type"] Lemma Z_to_le_bytes_split : forall a b z, (0 <= z)%Z ->
    Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
  Proof.
    induction a as [|a IH]; intros b z Hz.
    - cbn [Nat.add app Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
    - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH by (apply Z.shiftr_nonneg; lia). f_equal. f_equal.
      rewrite Z.shiftr_shiftr by lia. f_equal. lia.
  Qed.
  #[using="Type"] Lemma le8_pack2 : forall lo hi, le8 (pack2 lo hi) = le4 lo ++ le4 hi.
  Proof.
    intros lo hi. unfold pack2, le8, le4, word_to_le_bytes.
    pose proof (Z.mod_pos_bound (bv_unsigned lo) (2^32) ltac:(lia)) as H1.
    pose proof (Z.mod_pos_bound (bv_unsigned hi) (2^32) ltac:(lia)) as H2.
    rewrite unsigned_lit by lia. change 8%nat with (4 + 4)%nat at 1. rewrite Z_to_le_bytes_split by lia. f_equal.
    - rewrite <- (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned lo) 32) by (cbn; lia). f_equal.
      rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
    - rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned hi) 32) by (cbn; lia). f_equal.
      change (8 * Z.of_nat 4)%Z with 32%Z. rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma hdr3_bytes : forall h, cells_bytes (hdr3 h) = cells_bytes (hdr_cells h).
  Proof. intros h. cbn [cells_bytes cbytes hdr3 hdr_cells]. rewrite le8_pack2, <- app_assoc. reflexivity. Qed.
  #[using="Type"] Lemma hdr_cells_to_3 : forall m A h, rw_cells asegs m A (hdr_cells h) -> rw_cells asegs m A (hdr3 h).
  Proof. intros m A h HC. eapply rw_cells_recell; [exact HC| cbn; repeat split; exact I | apply hdr3_bytes]. Qed.
  #[using="Type"] Lemma hdr_cells_of_3 : forall m A h, rw_cells asegs m A (hdr3 h) -> rw_cells asegs m A (hdr_cells h).
  Proof. intros m A h HC. eapply rw_cells_recell; [exact HC| cbn; repeat split; exact I | symmetry; apply hdr3_bytes]. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma PCAPRg_blocks : forall P p PB rf st os m, PCAPRg P p PB rf st os m ->
    exists B I, PB = pcap_blocks p P B I.
  Proof. intros P p PB rf st os m (B & I & j & pad & bs & E & _). exists B, I. exact E. Qed.
  #[using="Type"] Lemma PCAPR_self_in : forall P p PB FB m, PCAPR P p PB FB m -> In (pc_self p, P, psize p) PB.
  Proof. intros P p PB FB m (Af & _ & (B & I & j & pad & bs & -> & _)). left. reflexivity. Qed.
  #[using="Type"] Lemma psize_pos : forall p, 664 <= psize p <= 680.
  Proof. intros p. unfold psize, PCAP_NG_SF_TOTAL, PCAP_SF_TOTAL. destruct (is_ng p); lia. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma priv_cells_size : forall p I pad, length pad = 4%nat ->
    cells_size (priv_cells p I pad) = (if is_ng p then 32 else 16)%nat.
  Proof. intros p I pad Hp. unfold priv_cells, is_ng. destruct (pc_priv p); cbn; reflexivity. Qed.
  #[using="Type"] Lemma priv_cells_size_le : forall m P p I pad, rw_cells asegs m P (priv_cells p I pad) -> (Z.of_nat (cells_size (priv_cells p I pad)) <= 32)%Z.
  Proof.
    intros m P p I pad [[Hwf _] _]. unfold priv_cells in *. destruct (pc_priv p); cbn in *; [lia|].
    destruct Hwf as (_ & _ & _ & _ & Hl & _). cbn in Hl. lia.
  Qed.
  #[using="Type"] Lemma if_cells_size : forall i j, cells_size (if_cells i j) = 40%nat.
  Proof. intros. reflexivity. Qed.
  #[using="Type"] Lemma ifs_cells_size : forall ifs js, length js = length ifs -> cells_size (ifs_cells ifs js) = (40 * length ifs)%nat.
  Proof.
    induction ifs as [|i ifs IH]; intros [|j0 js0] Hlen; cbn [length] in Hlen; try discriminate Hlen.
    - reflexivity.
    - cbn [ifs_cells]. rewrite cells_size_app, if_cells_size, (IH js0) by lia. cbn [length]. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma ifaces_ok_agree : forall p I m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    ifaces_ok p I m -> ifaces_ok p I m'.
  Proof.
    intros p I m m' Q AG HQ IFS. unfold ifaces_ok in *. destruct (pc_priv p) as [sf|sg [q|]] eqn:E; try exact IFS.
    destruct IFS as (js & tail & Hl & HC & H1 & H2 & H3 & H4). exists js, tail. split; [exact Hl|]. split; [|repeat split; try assumption; lia].
    eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. apply (HQ sg q eq_refl).
    pose proof (rw_cells_bound _ _ _ _ HC) as HB.
    rewrite cells_size_app in Ha, HB. cbn [cells_size csize] in Ha, HB. rewrite Nat.add_0_r in Ha, HB.
    rewrite ifs_cells_size in Ha by (rewrite length_rev; lia). rewrite length_rev in Ha. lia.
  Qed.
  #[using="Type"] Lemma priv_cells_psize : forall m A p I pad, rw_cells asegs m A (priv_cells p I pad) ->
    Z.of_nat (cells_size (priv_cells p I pad)) = psize p - PCAP_PRIV_OFF.
  Proof.
    intros m A p I pad [[Hwf _] _]. unfold priv_cells, psize, is_ng, PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL, PCAP_SF_TOTAL in *.
    destruct (pc_priv p); cbn in *; lia.
  Qed.
  #[using="Type"] Lemma pcap_aux_agree : forall p P B I pad bs m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall a, B <= a < B + pc_bufalloc p -> Q a) ->
    (forall a, P + PCAP_PRIV_OFF <= a < P + psize p -> Q a) ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    0 <= pc_bufalloc p ->
    rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> ifaces_ok p I m ->
    rw_cells asegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ rw_cells asegs m' (P + PCAP_PRIV_OFF) (priv_cells p I pad) /\ ifaces_ok p I m'.
  Proof.
    intros p P B I pad bs m m' Q AG HB HP HI Hba BUF PRIV IFS. split; [|split].
    - eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply HB. cbn [cells_size csize] in Ha. lia.
    - eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply HP. pose proof (priv_cells_psize _ _ _ _ _ PRIV). lia.
    - eapply ifaces_ok_agree; eassumption.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma pcap_cells_gen_size : forall p P B rf st os j, csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    cells_size (pcap_cells_gen p P B rf st os j) = 648%nat.
  Proof. intros p P B rf st os j H1 H2 H3. unfold pcap_cells_gen. rewrite !cells_size_app. cbn. rewrite H1, H2, H3. reflexivity. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma PCAPRg_agree : forall P p PB rf st os m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    PCAPRg P p PB rf st os m -> PCAPRg P p PB rf st os m'.
  Proof.
    intros P p PB rf st os m m' Q AG HQ Hrf Hst Hos (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF).
    exists B, I, j, pad, bs. split; [exact EPB|].
    pose proof (psize_pos p) as PS. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ. unfold PCAP_PRIV_OFF in PZ.
    pose proof WF as (_ & _ & W3 & _).
    assert (Q1 : forall a, P <= a < P + psize p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q2 : forall a, B <= a < B + pc_bufalloc p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q3 : forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a).
    { intros sg q Hq a Ha. apply HQ. rewrite EPB. unfold pcap_blocks. rewrite Hq. unfold in_block.
      do 2 apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    split. { eapply agrees_rw_cells; [exact AG|exact CELLS|]. intros a Ha. rewrite (pcap_cells_gen_size p P B rf st os j Hrf Hst Hos) in Ha. apply Q1. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply Q1. unfold PCAP_PRIV_OFF in Ha. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply Q2. cbn [cells_size csize] in Ha. lia. }
    split; [exact PFX|]. split; [|exact WF]. eapply ifaces_ok_agree; [exact AG| exact Q3| exact IFS].
  Qed.
  #[using="Type"] Lemma PCAPR_agree : forall P p PB FB m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> PCAPR P p PB FB m -> PCAPR P p PB FB m'.
  Proof.
    intros P p PB FB m m' Q AG HQ (Af & Hin & PG). exists Af. split; [exact Hin|].
    eapply PCAPRg_agree; [exact AG|exact HQ|reflexivity|reflexivity|reflexivity|exact PG].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma ifaces_ok_closable : forall p I m, ifaces_ok p I m -> ifaces_closable p I m.
  Proof.
    intros p I m HI. unfold ifaces_ok, ifaces_closable in *. destruct (pc_priv p) as [sf|s [q|]]; [exact HI| |tauto].
    destruct HI as (js & tail & Ljs & CE & E1 & E2 & E3 & E4). split; [|exact E3].
    rewrite <- (app_nil_r [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) tail]), app_assoc in CE.
    apply (rw_cells_merge asegs m I [] _ []) in CE. cbn [app] in CE. rewrite cells_size_app, ifs_cells_size in CE by (rewrite length_rev; lia).
    cbn [cells_size csize Nat.add] in CE. rewrite length_rev in CE.
    replace (40 * length (ng_ifaces s) + (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s)) + 0))%nat with (Z.to_nat (40 * ng_ifaces_size s)) in CE by lia.
    eexists. exact CE.
  Qed.
  #[using="Type"] Lemma PCAPR_closable_of : forall P p PB FB m, PCAPR P p PB FB m -> PCAPR_closable P p PB FB m.
  Proof.
    intros P p PB FB m (Af & Hin & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    exists Af. split; [exact Hin|]. exists B, I, j, pad, bs. repeat (split; [assumption|]). split; [apply ifaces_ok_closable; exact IFS| exact WF].
  Qed.
  #[using="Type"] Lemma ifaces_closable_agree : forall p I m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    ifaces_closable p I m -> ifaces_closable p I m'.
  Proof.
    intros p I m m' Q AG HQ IFS. unfold ifaces_closable in *. destruct (pc_priv p) as [sf|sg [q|]] eqn:E; try exact IFS.
    destruct IFS as ((junk & HC) & H3). split; [|exact H3]. exists junk.
    eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. apply (HQ sg q eq_refl). cbn [cells_size csize] in Ha. lia.
  Qed.
  #[using="Type"] Lemma PCAPRg_closable_agree : forall P p PB rf st os m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    PCAPRg_closable P p PB rf st os m -> PCAPRg_closable P p PB rf st os m'.
  Proof.
    intros P p PB rf st os m m' Q AG HQ Hrf Hst Hos (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF).
    exists B, I, j, pad, bs. split; [exact EPB|].
    pose proof (psize_pos p) as PS. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ. unfold PCAP_PRIV_OFF in PZ.
    pose proof WF as (_ & _ & W3 & _).
    assert (Q1 : forall a, P <= a < P + psize p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q2 : forall a, B <= a < B + pc_bufalloc p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q3 : forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a).
    { intros sg q Hq a Ha. apply HQ. rewrite EPB. unfold pcap_blocks. rewrite Hq. unfold in_block.
      do 2 apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    split. { eapply agrees_rw_cells; [exact AG|exact CELLS|]. intros a Ha. rewrite (pcap_cells_gen_size p P B rf st os j Hrf Hst Hos) in Ha. apply Q1. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply Q1. unfold PCAP_PRIV_OFF in Ha. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply Q2. cbn [cells_size csize] in Ha. lia. }
    split; [exact PFX|]. split; [|exact WF]. eapply ifaces_closable_agree; [exact AG| exact Q3| exact IFS].
  Qed.
  #[using="Type"] Lemma PCAPR_closable_agree : forall P p PB FB m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> PCAPR_closable P p PB FB m -> PCAPR_closable P p PB FB m'.
  Proof.
    intros P p PB FB m m' Q AG HQ (Af & Hin & PG). exists Af. split; [exact Hin|].
    eapply PCAPRg_closable_agree; [exact AG|exact HQ|reflexivity|reflexivity|reflexivity|exact PG].
  Qed.
  #[using="Type"] Lemma pcap_wf_set_header : forall p h, pcap_wf p -> 0 <= h_caplen h < 2^32 -> 0 <= h_len h < 2^32 -> pcap_wf (set_header h p).
  Proof. intros p h WF Hc Hl. unfold pcap_wf in *. destruct p; cbn in *. repeat split; try lia; tauto. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma PCAPR_intro_set_header : forall P p PB FB m h Af B I j pad bs,
    In (pc_rfile p, Af, FILE_BLOCK) FB -> PB = pcap_blocks p P B I ->
    rw_cells asegs m P (pcap_cells_gen (set_header h p) P B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j) ->
    rw_cells asegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> rw_cells asegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
    firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) -> ifaces_ok p I m -> pcap_wf p ->
    0 <= h_caplen h < 2^32 -> 0 <= h_len h < 2^32 ->
    PCAPR P (set_header h p) PB FB m.
  Proof.
    intros P p PB FB m h Af B I j pad bs Hin EPB HC HP HB PFX IFS WF Hc Hl.
    pose proof (pcap_wf_set_header p h WF Hc Hl) as WF'.
    exists Af. split; [destruct p; exact Hin|]. exists B, I, j, pad, bs.
    split; [destruct p; exact EPB|]. split; [exact HC|]. split; [destruct p; exact HP|]. split; [destruct p; exact HB|].
    split; [destruct p; exact PFX|]. split; [destruct p; exact IFS| exact WF'].
  Qed.
End Rep.
End TwB.
