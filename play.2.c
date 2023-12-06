
/* 
 * play.2.c -- The perfect Havannah-3 Player.
 *
 * Based on a complete table in file 'play.2.dat'.
 *
 * Compilation: gcc -Wall -Werror -std=c99 -O3 play.2.c -o play.2.bin -lz
 *
 * Author: Mirko Rahn, mirko.rahn@web.de
 *
 */

/* ************************************************************************* */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <zlib.h>

/* ************************************************************************* */

#define ERROR(FMT,...) fprintf(stderr, "ERROR: "FMT"\n", ##__VA_ARGS__); \
                       exit(EXIT_FAILURE)
#define STRANGE(FMT,...) free (buf); ERROR("STRANGE! "FMT"!?", ##__VA_ARGS__)
#define UNKNOWN_ENUM(descr,x) STRANGE("Unknown %s: %d", descr, (int)x)

/* ************************************************************************* */

#define ERROR_FGETS STRANGE("Reading input failed")

static char linebuf[22];

#define FGETS \
  if (fgets (linebuf, 20, stdin) == NULL) { ERROR_FGETS; }; fflush (stdin)

/* ************************************************************************* */

static void * buf = NULL;
static const uint32_t * dat = NULL;
static const uint8_t * res = NULL;
static const uint32_t * bucket = NULL;
static const int8_t * depth = NULL;

static uint32_t
bin_search (uint32_t game, uint32_t slot)
{
  uint32_t l = bucket[slot];
  uint32_t r = bucket[slot+1];

  while (r >= l)
    {
      uint32_t c = ((r + l) >> 1);

      if (game < dat[c])
	{
	  r = c-1;
	}
      else
	{
	  l = c+1;
	}

      if (game == dat[c])
	{
	  return c;
	}
    }

  STRANGE ("Game %u %u unknown", game, slot);
}

/* ************************************************************************* */

typedef enum {False,True} Bool;
typedef enum {A,B,X} Player;
typedef enum {Fork,Bridge,Ring,None} Figure;
typedef struct {Player player;Figure figure;Bool finished;} Result;
typedef uint8_t Field;
typedef uint8_t Coord;
typedef struct {Coord x; Coord y;} Point;
typedef uint32_t Num[2];
typedef Num Board[12+1];

#define DIV_CONTAINER_SIZE(x) ((x) >> 5)
#define MOD_CONTAINER_SIZE(x) ((x) &  31)

#define THE_NORM(norm) norm[12]
#define THE_BOARD(norm) norm[0]

#define FOR_NORM(id) for (int id = 0; id < 12; ++id)
#define FOR_CONTAINER(id) for (int id = 0; id < 2; ++id)
#define FOR_FIELD(id) for (Field id = 0; id < 19; ++id)

static Player
other (Player player)
{
  return (player == A) ? B : A;
}

static char
show_Player (Player player)
{
  switch (player)
    {
    case A: return 'A'; break;
    case B: return 'B'; break;
    case X: return '.'; break;
    default: UNKNOWN_ENUM("Player",player); break;
    }
}

static char *
show_Figure (Figure figure)
{
  switch (figure)
    {
    case Fork: return "Fork"; break;
    case Bridge: return "Bridge"; break;
    case Ring: return "Ring"; break;
    case None: return "None"; break;
    default: UNKNOWN_ENUM("Figure",figure);break;
    }
}

static const Field const equiv[12][19] = 
  {{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18}
  ,{0,3,7,1,4,8,12,2,5,9,13,16,6,10,14,17,11,15,18}
  ,{2,1,0,6,5,4,3,11,10,9,8,7,15,14,13,12,18,17,16}
  ,{2,6,11,1,5,10,15,0,4,9,14,18,3,8,13,17,7,12,16}
  ,{7,3,0,12,8,4,1,16,13,9,5,2,17,14,10,6,18,15,11}
  ,{7,12,16,3,8,13,17,0,4,9,14,18,1,5,10,15,2,6,11}
  ,{11,6,2,15,10,5,1,18,14,9,4,0,17,13,8,3,16,12,7}
  ,{11,15,18,6,10,14,17,2,5,9,13,16,1,4,8,12,0,3,7}
  ,{16,12,7,17,13,8,3,18,14,9,4,0,15,10,5,1,11,6,2}
  ,{16,17,18,12,13,14,15,7,8,9,10,11,3,4,5,6,0,1,2}
  ,{18,15,11,17,14,10,6,16,13,9,5,2,12,8,4,1,7,3,0}
  ,{18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0}
  };

static const Point const coord[19] = 
  {{0,6},{0,4},{0,2},{2,7},{2,5},{2,3},{2,1},{4,8},{4,6},{4,4}
  ,{4,2},{4,0},{6,7},{6,5},{6,3},{6,1},{8,6},{8,4},{8,2}
  };

static const char * const show_Field[] =
  {"A1","A2","A3","B1","B2","B3","B4","C1","C2","C3"
  ,"C4","C5","D1","D2","D3","D4","E1","E2","E3"
  };

static const Field Field_invalid = 19;

static Field
read_Field (char str[2])
{
  switch (str[0])
    {
    case 'a': case 'A': switch (str[1])
	{
	case '1': return 0; break;
	case '2': return 1; break;
	case '3': return 2; break;
	default: return Field_invalid; break;
	}
      break;
    case 'b': case 'B': switch (str[1])
	{
	case '1': return 3; break;
	case '2': return 4; break;
	case '3': return 5; break;
	case '4': return 6; break;
	default: return Field_invalid; break;
	}
      break;
    case 'c': case 'C': switch (str[1])
	{
	case '1': return 7; break;
	case '2': return 8; break;
	case '3': return 9; break;
	case '4': return 10; break;
	case '5': return 11; break;
	default: return Field_invalid; break;
	}
      break;
    case 'd': case 'D': switch (str[1])
	{
	case '1': return 12; break;
	case '2': return 13; break;
	case '3': return 14; break;
	case '4': return 15; break;
	default: return Field_invalid; break;
	}
      break;
    case 'e': case 'E': switch (str[1])
	{
	case '1': return 16; break;
	case '2': return 17; break;
	case '3': return 18; break;
	default: return Field_invalid; break;
	}
      break;
    default: return Field_invalid; break;
    }
}

static Result
read_Result (uint8_t result)
{
  switch (result)
    {
    case 0:  return (Result){X,  None,False} ;break;
    case 1:  return (Result){X,  None, True} ;break;
    case 2:  return (Result){A,  None,False} ;break;
    case 3:  return (Result){A,Bridge, True} ;break;
    case 4:  return (Result){A,  Fork, True} ;break;
    case 5:  return (Result){A,  Ring, True} ;break;
    case 6:  return (Result){A,  Ring, True} ;break;
    case 7:  return (Result){B,  None,False} ;break;
    case 8:  return (Result){B,Bridge, True} ;break;
    case 9:  return (Result){B,  Fork, True} ;break;
    case 10: return (Result){B,  Ring, True} ;break;
    case 11: return (Result){B,  Ring, True} ;break;
    default: UNKNOWN_ENUM("Result",result); break;
    }
}

static Field
num_bit (Player player, Field field)
{
  return (player == A) ? (field + 1) : (field + 20);
}

static Bool
num_less (Num x, Num y)
{
  FOR_CONTAINER(c)
    {
      if (x[c] < y[c])
	{
	  return True;
	}
      else if (x[c] > y[c])
	{
	  return False;
	}
    }

  return False;
}

static void
num_copy (Num dest, Num src)
{
  FOR_CONTAINER(c)
    {
      dest[c] = src[c];
    }
}

static void
num_clear (Num num)
{
  FOR_CONTAINER(c)
    {
      num[c] = 0;
    }
}

static void
num_max (Num num)
{
  FOR_CONTAINER(c)
    {
      num[c] = ~0;
    }
}

static void
num_set_bit (Num num, int8_t bit)
{
  int8_t q = DIV_CONTAINER_SIZE(bit);
  int8_t r = MOD_CONTAINER_SIZE(bit);

  num[q] |= (1<<r); 
}

static void
num_clear_bit (Num num, int8_t bit)
{
  int8_t q = DIV_CONTAINER_SIZE(bit);
  int8_t r = MOD_CONTAINER_SIZE(bit);

  num[q] &= ~(1<<r); 
}

static Bool
num_get_bit (Num num, int8_t bit)
{
  int8_t q = DIV_CONTAINER_SIZE(bit);
  int8_t r = MOD_CONTAINER_SIZE(bit);

  return (((num[q] >> r) & 1) == 1) ? True : False;
}

static Player
num_get_to_move (Num num)
{
  return (num_get_bit(num, 0) == True) ? B : A;
}


static void
num_set_to_move (Num num, Player player)
{
  if (player == B) 
    {
      num_set_bit (num, 0);
    }
  else
    {
      num_clear_bit (num, 0);
    }
}

static void
num_put (Num num, Field field)
{
  num_set_bit (num, num_bit(num_get_to_move(num), field));
  num_set_to_move (num, other(num_get_to_move(num)));
}

static void
num_unput (Num num, Field field)
{
  num_clear_bit (num, num_bit(other(num_get_to_move(num)), field));
  num_set_to_move (num, other(num_get_to_move(num)));
}

static Player
num_stone (Num num, Field field)
{
  if (num_get_bit(num, num_bit(A, field)) == True) { return A; }
  if (num_get_bit(num, num_bit(B, field)) == True) { return B; }

  return X;
}

static void
num_printf_board (Num num)
{
  char board[9][9] = 
    {"         ","         ","         ","         ","         "
    ,"         ","         ","         ","         "
    };

  FOR_FIELD(field)
    {
      board[coord[field].x][coord[field].y] 
	= show_Player(num_stone(num, field));
    }

  for (int8_t row = 0; row < 9; ++row)
    {
      for (int8_t col = 0; col < 9; ++col)
	{
	  printf (" %c", board[col][row]);
	}

      printf ("\n");
    }
}

static void
board_clear (Board board)
{
  FOR_NORM(n)
    {
      num_clear(board[n]);
    }

  num_clear(THE_NORM(board));
}

static void
board_put (Board board, Field field)
{
  num_max(THE_NORM(board));

  FOR_NORM(n)
    {
      num_put(board[n], equiv[n][field]);

      if (num_less(board[n],THE_NORM(board)) == True)
	{
	  num_copy(THE_NORM(board), board[n]);
	}
    }
}

static void
board_unput (Board board, Field field)
{
  num_max(THE_NORM(board));

  FOR_NORM(n)
    {
      num_unput(board[n], equiv[n][field]);

      if (num_less(board[n],THE_NORM(board)) == True)
	{
	  num_copy(THE_NORM(board), board[n]);
	}
    }
}

static Result
board_result (Board board)
{
  return read_Result(res[bin_search(THE_NORM(board)[0], THE_NORM(board)[1])]);
}

static int
board_depth (Board board)
{
  return depth[bin_search(THE_NORM(board)[0], THE_NORM(board)[1])];
}

/* ************************************************************************* */

static Player opponent;

static void
play (Board board)
{
  printf ("The position is:\n");

  num_printf_board(THE_BOARD(board));

  Result result = board_result (board);

  if (result.finished)
    {
      if (result.player == opponent)
	{
	  printf ("There is a %s. You won.\n", show_Figure(result.figure));
	}
      else if (result.player == other(opponent))
	{
	  printf ("There is a %s. You lost.\n", show_Figure(result.figure));
	}
      else
	{
	  printf ("Draw.\n");
	}
    }
  else
    {
      Player to_move = num_get_to_move(THE_BOARD(board));

      if (to_move == opponent)
	{
	  Field to_put = Field_invalid;

	MOVE:
	  printf ("Please enter your move: [");

	  FOR_FIELD(field)
	    {
	      if (num_stone(THE_BOARD(board), field) == X)
		{
		  printf ("%s,", show_Field[field]);
		}
	    }

	  printf ("Resign] ");

	  FGETS;

	  switch (linebuf[0])
	    {
	    case 'r': case 'R':
	      printf ("Resign? [y/N] ");

	      FGETS;
	      
	      if (linebuf[0] == 'y' || linebuf[1] == 'Y')
		{
		  return;
		}

	      goto MOVE;

	      break;

	    default: to_put = read_Field(linebuf); break;
	    }

	  if (to_put == Field_invalid)
	    {
	      goto MOVE;
	    }

	  if (num_stone(THE_BOARD(board), to_put) != X)
	    {
	      goto MOVE;
	    }

	  board_put (board, to_put);

	  play (board);
	}
      else
	{
	  int8_t suc_depth_all[19];
	  Field suc_field_all[19];
	  uint8_t suc_all = 0;
	  int8_t suc_depth_minimum =  127;
	  int8_t suc_depth_maximum = -128;

	  FOR_FIELD(field)
	    {
	      if (num_stone(THE_BOARD(board), field) == X)
		{
		  board_put (board, field);

		  suc_depth_all[suc_all] = board_depth(board);
		  suc_field_all[suc_all] = field;

		  if (suc_depth_all[suc_all] > suc_depth_maximum)
		    {
		      suc_depth_maximum = suc_depth_all[suc_all];
		    }

		  if (suc_depth_all[suc_all] < suc_depth_minimum)
		    {
		      Result suc_result = board_result (board);

		      if (suc_result.player != opponent)
			{
			  suc_depth_minimum = suc_depth_all[suc_all];
			}
		    }

		  suc_all += 1;

		  board_unput (board, field);
		}
	    }

	  if (suc_all == 0)
	    {
	      STRANGE ("No move in non-finished position");
	    }

	  Field suc_field[19];
	  int8_t suc = 0;
	  int8_t depth_wanted =
	    (result.player == opponent) ? suc_depth_maximum : suc_depth_minimum;

	  for (uint8_t s = 0; s < suc_all; ++s)
	    {
	      if (suc_depth_all[s] == depth_wanted)
		{
		  suc_field[suc++] = suc_field_all[s];
		}
	    }

	  if (suc == 0)
	    {
	      STRANGE ("No minimal/maximal depth move");
	    }

	  Field to_put = suc_field[rand() % suc];

	  printf ("The computer plays %s.\n", show_Field[to_put]);
	  
	  board_put (board, to_put);

	  play (board);
	}
    }
}

/* ************************************************************************* */

int main ()
{
  printf ("Welcome. This is the perfect Havannah-3 player.\n");
  printf ("Reading tables..."); fflush (stdout);

  srand (time(NULL));

  buf = malloc (99473396);

  if (buf == NULL)
    {
      ERROR ("Allocate memory.");
    }

  gzFile * fbin = gzopen ("play.2.dat", "r");

  if (fbin != NULL)
    {
      if (gzread (fbin, buf, 99473396) != 99473396)
	{
	  ERROR ("Read tables.");
	}
    }

  gzclose (fbin);

  bucket = buf + 0;
  dat = buf + 512;
  res = buf + 66315768;
  depth = buf + 82894582;

  printf ("[done]\n");

 GAME:
  opponent = A;

  printf ("Do you want to play first? [Y/n] ");

  FGETS;

  switch (linebuf[0])
    {
    case 'n': case 'N': opponent = B; break;
    default: break;
    }

  Board board; board_clear(board);

  play (board);

  printf ("Do you want to play another one? [Y/n] ");

  FGETS;

  if (linebuf[0] != 'n' && linebuf[0] != 'N') 
    {
      goto GAME;
    }

  printf ("Thank you for playing.\n");

  free (buf);

  return EXIT_SUCCESS;
}
