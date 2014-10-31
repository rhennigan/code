/*
 ********************************************************************************
 * player.h
 * Richard Hennigan
 ********************************************************************************
 */

#ifndef _PLAYER_H
#define _PLAYER_H

#include <stdlib.h>
#include <string.h>
#include "data/circular_linked_list.h"

typedef struct player_s {
  int num;
  char * name;
  int score;
  bool control;
} _player_t;

typedef _player_t (*player_t);

def_clist_base(player_t);


bool
player_cmp(player_t player1, player_t player2)
{
  assert(player1);
  assert(player2);
  bool same_name = strcmp(player1->name, player2->name) == 0;
  return same_name;
}



void
player_print(player_t player)
{
  assert(player);
  char * control = player->control ? "AI" : "H";
  printf("  %d\t%s\t%d\t%s\n", player->num, control, player->score, player->name);
}


void
show_player_list(player_t_clist_t * player_list)
{
  printf("\n");
  printf("  PLAYERS\n");
  printf("  ----------------------------------------\n");
  printf("  Num\tCtrl\tPts\tName\n");
  printf("  ----------------------------------------\n");
  player_t_clist_iter(player_list, (*player_print));
  printf("  ----------------------------------------\n");
  printf("\n");
  fflush(stdout);
}


player_t
player_new(int num, char * name, int score, bool control)
{
  player_t player = (player_t) malloc (sizeof (_player_t));
  player->num = num;
  player->name = name;
  player->score = score;
  player->control = control;
  
  return player;
}


int
player_score(player_t player)
{
  assert(player);
  return player->score;
}

typedef struct {
  char * name;
} name_t;

typedef char * str;

def_clist_base(str);
def_clist_full(int, "%d");
def_clist_map(player_t, int);
def_clist_map(player_t, str);


str
player_name(player_t player)
{
  assert(player);
  return player->name;
}

def_clist_print(str, "%s");

#endif
